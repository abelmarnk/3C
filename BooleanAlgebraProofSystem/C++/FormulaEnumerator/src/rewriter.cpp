#include "formula_enumerator/rewriter.hpp"

#include <algorithm>
#include <climits>
#include <memory>
#include <random>

#include "formula_enumerator/laws.hpp"
#include "formula_enumerator/symbols.hpp"

namespace fe {

namespace {
/*
 * erase_span
 * ----------------
 * Remove `count` elements from formula `f` starting at position `start`.
 * This is a low-level helper used by rewrite rules to delete subexpressions
 * (for contractions or when replacing nodes). It assumes indices are valid
 * and performs an in-place erase on the vector representing the prefix
 * formula.
 */
void erase_span(Formula& f, const int start, const int count) {
    f.erase(f.begin() + start, f.begin() + start + count);
}

/*
 * insert_values
 * ----------------
 * Insert a small list of integer symbols into formula `f` at position `pos`.
 * Used by expansion rewrite rules which need to introduce operator tokens
 * and their operands (e.g., turning `a` into `OR a FALSE`). This is a
 * thin wrapper around `vector::insert` for readability.
 */
void insert_values(Formula& f, const int pos, const std::initializer_list<int> values) {
    f.insert(f.begin() + pos, values.begin(), values.end());
}

/*
 * ensure_capacity
 * ----------------
 * Check whether an expansion that would add `extra` symbols to `f`
 * would remain within the allowed `max_length`. Many rewrite rules
 * attempt to expand a node; they must guard with this function to
 * prevent unbounded growth beyond the allotted padding-based limit.
 */
bool ensure_capacity(const Formula& f, const int max_length, const int extra) {
    return static_cast<int>(f.size()) + extra <= max_length;
}

/*
 * increment_variable_count
 * -------------------------
 * Maintain reference counts in `variables_in_use` when a rewrite
 * expansion duplicates or introduces a variable/subexpression.
 * - If `variable_name` is not a variable token, do nothing.
 * - If it's new in the map, insert with count=1 and kind=0 (plain).
 * - Otherwise increment the stored count and recursively increment
 *   any dependent variables if this variable is an alias (kind==1 => NOT,
 *   kind>=2 => binary operator with operands `a` and `b`).
 *
 * This ensures `variables_in_use` tracks transitive multiplicity so that
 * substitution and cleanup operations can be performed safely.
 */
void increment_variable_count(const int variable_name, VariableMap& variables_in_use) {
    if (!is_variable(variable_name)) {
        return;
    }

    auto it = variables_in_use.find(variable_name);
    if (it == variables_in_use.end()) {
        variables_in_use[variable_name] = SubExpression{1, 0, 0, 0};
        return;
    }

    ++it->second.count;

    if (it->second.kind == 1) {
        increment_variable_count(it->second.a, variables_in_use);
    } else if (it->second.kind >= 2) {
        increment_variable_count(it->second.a, variables_in_use);
        increment_variable_count(it->second.b, variables_in_use);
    }
}

/*
 * Decrease the reference count for `variable_name` and optionally cascade
 * the decrement into dependent subexpressions. Behavior:
 * - If name not present, do nothing.
 * - Copy the stored SubExpression, decrement its count.
 * - If `cascading` is true and this SubExpression is an alias, recursively
 *   decrement its operand(s).
 * - If the decremented count reaches zero, remove the entry from the map;
 *   otherwise write the updated SubExpression back (so dependent fields
 *   remain intact).
 *
 * This function is the counterpart to `increment_variable_count` and
 * preserves the invariant that the map reflects the current multiplicity
 * of variables and alias usage.
 */
void decrement_variable_count(const int variable_name, VariableMap& variables_in_use, const bool cascading) {
    const auto it = variables_in_use.find(variable_name);
    if (it == variables_in_use.end()) {
        return;
    }

    SubExpression sub = it->second;
    --sub.count;

    if (cascading && sub.kind == 1) {
        decrement_variable_count(sub.a, variables_in_use, true);
    } else if (cascading && sub.kind >= 2) {
        decrement_variable_count(sub.a, variables_in_use, true);
        decrement_variable_count(sub.b, variables_in_use, true);
    }

    if (sub.count <= 0) {
        variables_in_use.erase(it);
    } else {
        variables_in_use[variable_name] = sub;
    }
}

/*
 * new_random_variable_name
 * -------------------------
 * Generate a fresh integer token to represent a new synthetic variable
 * (used by substitution rules). The generated value is >= MIN_VARIABLE and
 * is chosen randomly from the 32-bit integer range. The function loops
 * until it finds a name not already present in `variables_in_use` to avoid
 * collisions with existing aliases.
 */
int new_random_variable_name(const VariableMap& variables_in_use) {
    static std::mt19937 rng{std::random_device{}()};
    std::uniform_int_distribution<int> dist(MIN_VARIABLE, INT_MAX);

    int variable_name = MIN_VARIABLE;
    do {
        variable_name = dist(rng);
    } while (variables_in_use.find(variable_name) != variables_in_use.end());
    return variable_name;
}

/*
 * Implements the identity law for OR:
 *   - Contract: OR a FALSE -> a
 *   - Expand:   a -> OR a FALSE (when capacity permits)
 *
 * The contraction reduces size and is used to simplify formulas. The
 * expansion is used by the proof search to introduce an OR context so
 * other laws can match (e.g., distributive or idempotent patterns). The
 * expansion must respect `max_length` to avoid uncontrolled growth.
 */
bool is_identity_or(Formula& f, const int max_length, const int s) {
    // Contract
    if (static_cast<int>(f.size()) > s + 3 && f[s] == OR && is_boolean(f[s + 1]) && f[s + 2] == FALSE_VALUE) {
        f[s] = f[s + 1];
        erase_span(f, s + 1, 2);
        return true;
    }
    // Expand
    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 2)) {
        const int a = f[s];
        insert_values(f, s + 1, {a, FALSE_VALUE});
        f[s] = OR;
        return true;
    }
    return false;
}

/*
 * Implements the identity law for AND:
 *   - Contract: AND a TRUE -> a
 *   - Expand:   a -> AND a TRUE (when capacity permits)
 *
 * Mirrors `is_identity_or` but for AND. Useful for simplifying and for
 * creating AND contexts to enable other rule matches.
 */
bool is_identity_and(Formula& f, const int max_length, const int s) {
    // Contract
    if (static_cast<int>(f.size()) > s + 3 && f[s] == AND && is_boolean(f[s + 1]) && f[s + 2] == TRUE_VALUE) {
        f[s] = f[s + 1];
        erase_span(f, s + 1, 2);
        return true;
    }
    // Expand
    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 2)) {
        const int a = f[s];
        insert_values(f, s + 1, {a, TRUE_VALUE});
        f[s] = AND;
        return true;
    }
    return false;
}

/*
 * Implements idempotence for OR:
 *   - Contract: OR a a -> a (removes duplicate operand)
 *     - Calls `decrement_variable_count` to update bookkeeping.
 *   - Expand:   a -> OR a a (introduces a duplicate)
 *     - Calls `increment_variable_count` for bookkeeping.
 *
 * Contraction reduces redundancy and can shorten proofs; expansion
 * creates duplicates that may enable substitution or other pattern
 * matches. The bookkeeping keeps `variables_in_use` consistent.
 */
bool is_idempotent_or(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    // Contract
    if (static_cast<int>(f.size()) > s + 3 && f[s] == OR && is_boolean(f[s + 1]) && f[s + 1] == f[s + 2]) {
        const int a = f[s + 1];
        f[s] = a;
        erase_span(f, s + 1, 2);
        decrement_variable_count(a, variables_in_use, true);
        return true;
    }
    // Expand
    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 2)) {
        const int a = f[s];
        insert_values(f, s + 1, {a, a});
        f[s] = OR;
        increment_variable_count(a, variables_in_use);
        return true;
    }
    return false;
}

/*
 * Implements idempotence for AND (mirror of `is_idempotent_or`).
 * Contract: AND a a -> a (calls `decrement_variable_count`).
 * Expand:   a -> AND a a (calls `increment_variable_count`).
 */
bool is_idempotent_and(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    // Contract
    if (static_cast<int>(f.size()) > s + 3 && f[s] == AND && is_boolean(f[s + 1]) && f[s + 1] == f[s + 2]) {
        const int a = f[s + 1];
        f[s] = a;
        erase_span(f, s + 1, 2);
        decrement_variable_count(a, variables_in_use, true);
        return true;
    }
    // Expand
    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 2)) {
        const int a = f[s];
        insert_values(f, s + 1, {a, a});
        f[s] = AND;
        increment_variable_count(a, variables_in_use);
        return true;
    }
    return false;
}

/*
 * Swap the two operands of a binary operator (OR or AND) at position `s`.
 * This is a syntactic reorder only (no capacity or bookkeeping changes).
 * Permuting operands is crucial so other pattern-matching rules can
 * succeed regardless of operand order.
 * Swap: OR a b <-> OR b a (Same applies to AND)
 */
bool is_commutative(Formula& f, const int s) {
    if (static_cast<int>(f.size()) > s + 3 && (f[s] == OR || f[s] == AND) && is_boolean(f[s + 1]) && is_boolean(f[s + 2])) {
        std::swap(f[s + 1], f[s + 2]);
        return true;
    }
    return false;
}

/*
 * Perform a local reassociation by swapping operands in nested patterns.
 * The function recognizes shapes where reassociation may enable other
 * rewrites (e.g., distributivity). It only performs a local swap and
 * does not change semantics; it helps normalize grouping so other
 * indexed rewrite attempts can match.
 * Swap:- OR OR a b c <-> OR b OR a c (Same applies to AND)
 */
bool is_associative(Formula& f, const int s) {
    if (static_cast<int>(f.size()) > s + 5 &&
        (f[s] == OR || f[s] == AND) &&
        (is_boolean(f[s + 1]) || is_boolean(f[s + 2])) &&
        (f[s + 1] == f[s] || f[s + 2] == f[s]) &&
        is_boolean(f[s + 3]) && is_boolean(f[s + 4])) {
        std::swap(f[s + 1], f[s + 2]);
        return true;
    }
    return false;
}

/*
 * Handles distributivity in both directions. There are two primary
 * patterns implemented:
 *  - Expand:  OR a (AND b c)  ->  AND (OR a b) (OR a c)  (and the dual)
 *    This expansion increases formula size and therefore checks
 *    `ensure_capacity` before making the change. After inserting the
 *    new symbols we call `increment_variable_count` for any duplicated
 *    operand to keep bookkeeping correct.
 *  - Contract: a OP (OP a b) -> (reassociate/contract) -- the second
 *    branch recognizes the inverse pattern and reduces formula size,
 *    calling `decrement_variable_count` as needed.
 */
bool is_distributive(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    // Expand
    if (static_cast<int>(f.size()) > s + 5 &&
        ((f[s] == OR && f[s + 2] == AND) || (f[s] == AND && f[s + 2] == OR)) &&
        is_boolean(f[s + 1]) && is_boolean(f[s + 3]) && is_boolean(f[s + 4])) {
        if (!ensure_capacity(f, max_length, 2)) {
            return false;
        }
        const int a = f[s + 1];
        const int b = f[s + 3];
        const int c = f[s + 4];
        const int outer = f[s];
        const int inner = f[s + 2];

        // OR a AND b c -> AND OR a b OR a c (and dual)
        f[s] = inner;
        f[s + 1] = outer;
        f[s + 2] = a;
        f[s + 3] = b;
        f[s + 4] = outer;
        insert_values(f, s + 5, {a, c});
        increment_variable_count(a, variables_in_use);
        return true;
    }

    // Contract
    if (static_cast<int>(f.size()) > s + 7 &&
        ((f[s] == AND && f[s + 1] == OR && f[s + 4] == OR) ||
         (f[s] == OR && f[s + 1] == AND && f[s + 4] == AND)) &&
        is_boolean(f[s + 2]) && is_boolean(f[s + 3]) && is_boolean(f[s + 6]) &&
        f[s + 2] == f[s + 5]) {
        const int outer = f[s];
        const int inner = f[s + 1];
        const int a = f[s + 2];
        const int b = f[s + 3];
        const int c = f[s + 6];

        // Contract the dual distributive shape back to a simpler form.
        f[s] = inner;
        f[s + 1] = a;
        f[s + 2] = outer;
        f[s + 3] = b;
        f[s + 4] = c;
        erase_span(f, s + 5, 2);
        decrement_variable_count(a, variables_in_use, true);
        return true;
    }

    return false;
}

/*
 * Implements De Morgan transformations and the push/pop of NOT across
 * binary operators. Two directions:
 *  - Push NOT inward: NOT (OR a b) -> AND (NOT a) (NOT b) (and dual)
 *    This expands the representation and is guarded by capacity.
 *  - Pull NOT outward: (AND NOT a NOT b) -> NOT (OR a b) (dual)
 *    This contracts by removing redundant NOTs and changing the
 *    surrounding operator.
 */
bool is_demorgan(Formula& f, const int max_length, const int s) {
    // Push NOT inward
    if (static_cast<int>(f.size()) > s + 4 && f[s] == NOT && is_boolean(f[s + 2]) && is_boolean(f[s + 3])) {
        if (!ensure_capacity(f, max_length, 1)) {
            return false;
        }
        const int op = f[s + 1];
        if (op != OR && op != AND) {
            return false;
        }
        const int a = f[s + 2];
        const int b = f[s + 3];
        f[s] = (op == OR) ? AND : OR;
        f[s + 1] = NOT;
        f[s + 2] = a;
        f[s + 3] = NOT;
        insert_values(f, s + 4, {b});
        return true;
    }

    // Push NOT outward    
    if (static_cast<int>(f.size()) > s + 5 && f[s + 1] == NOT && is_boolean(f[s + 2]) && f[s + 3] == NOT && is_boolean(f[s + 4])) {
        if (f[s] == AND || f[s] == OR) {
            const int a = f[s + 2];
            const int b = f[s + 4];
            const int op = (f[s] == AND) ? OR : AND;
            f[s] = NOT;
            f[s + 1] = op;
            f[s + 2] = a;
            f[s + 3] = b;
            erase_span(f, s + 4, 1);
            return true;
        }
    }

    return false;
}

/*
 * Complement/negation propagation rules and small constant rewrites.
 * Examples:
 *  - OR a (NOT a) <-> TRUE
 *  - AND a (NOT a) <-> FALSE
 * The function also provides small expansions that introduce NOT and
 * constant contexts when capacity permits.
 */
bool is_complement(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    // Contract
    if (static_cast<int>(f.size()) > s + 4 && is_boolean(f[s + 1]) && f[s + 2] == NOT && f[s + 1] == f[s + 3]) {
        const int a = f[s + 1];
        if (f[s] == OR) {
            f[s] = TRUE_VALUE;
            erase_span(f, s + 1, 3);
            decrement_variable_count(a, variables_in_use, true);
            decrement_variable_count(a, variables_in_use, true);
            return true;
        }
        if (f[s] == AND) {
            f[s] = FALSE_VALUE;
            erase_span(f, s + 1, 3);
            decrement_variable_count(a, variables_in_use, true);
            decrement_variable_count(a, variables_in_use, true);
            return true;
        }
    }

    // Expand
    if (ensure_capacity(f, max_length, 3)) {
        if (f[s] == TRUE_VALUE) {
            f[s] = OR;
            insert_values(f, s + 1, {TRUE_VALUE, NOT, TRUE_VALUE});
            return true;
        }
        if (f[s] == FALSE_VALUE) {
            f[s] = AND;
            insert_values(f, s + 1, {TRUE_VALUE, NOT, TRUE_VALUE});
            return true;
        }
    }

    return false;
}

/*
 * Domination rules: simplify when a neutralizing constant is present
 * (e.g., OR x TRUE <-> TRUE, AND x FALSE <-> FALSE). Also supports the
 * inverse expansions that introduce duplicate constants when capacity
 * allows.
 */
bool is_domination(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    if (static_cast<int>(f.size()) > s + 3 && is_boolean(f[s + 1])) {
        if (f[s] == OR && f[s + 2] == TRUE_VALUE) {
            decrement_variable_count(f[s + 1], variables_in_use, true);
            f[s] = TRUE_VALUE;
            erase_span(f, s + 1, 2);
            return true;
        }
        if (f[s] == AND && f[s + 2] == FALSE_VALUE) {
            decrement_variable_count(f[s + 1], variables_in_use, true);
            f[s] = FALSE_VALUE;
            erase_span(f, s + 1, 2);
            return true;
        }
    }

    if (ensure_capacity(f, max_length, 2)) {
        if (f[s] == TRUE_VALUE) {
            f[s] = OR;
            insert_values(f, s + 1, {TRUE_VALUE, TRUE_VALUE});
            return true;
        }
        if (f[s] == FALSE_VALUE) {
            f[s] = AND;
            insert_values(f, s + 1, {FALSE_VALUE, FALSE_VALUE});
            return true;
        }
    }

    return false;
}

/*
 * Absorption law (OR): OR a (AND a b) <-> a and the controlled expansion
 * that introduces an absorption-shaped context when capacity permits.
 */
bool is_absorption_or(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    if (static_cast<int>(f.size()) > s + 5 && f[s] == OR && is_boolean(f[s + 1]) && f[s + 2] == AND && f[s + 1] == f[s + 3] && is_boolean(f[s + 4])) {
        const int a = f[s + 1];
        const int b = f[s + 4];
        f[s] = a;
        erase_span(f, s + 1, 4);
        decrement_variable_count(a, variables_in_use, true);
        decrement_variable_count(b, variables_in_use, true);
        return true;
    }

    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 4)) {
        const int a = f[s];
        f[s] = OR;
        insert_values(f, s + 1, {a, AND, a, TRUE_VALUE});
        increment_variable_count(a, variables_in_use);
        return true;
    }

    return false;
}

/*
 * Absorption law (AND): AND a (OR a b) -> a and the controlled expansion
 * that introduces an absorption-shaped context when capacity permits.
 */
bool is_absorption_and(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    if (static_cast<int>(f.size()) > s + 5 && f[s] == AND && is_boolean(f[s + 1]) && f[s + 2] == OR && f[s + 1] == f[s + 3] && is_boolean(f[s + 4])) {
        const int a = f[s + 1];
        const int b = f[s + 4];
        f[s] = a;
        erase_span(f, s + 1, 4);
        decrement_variable_count(a, variables_in_use, true);
        decrement_variable_count(b, variables_in_use, true);
        return true;
    }

    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 4)) {
        const int a = f[s];
        f[s] = AND;
        insert_values(f, s + 1, {a, OR, a, FALSE_VALUE});
        increment_variable_count(a, variables_in_use);
        return true;
    }

    return false;
}

/*
 * Double-negation elimination/introduction: NOT NOT a <-> a and the
 * controlled expansion a -> NOT NOT a.
 */
bool is_double_negation(Formula& f, const int max_length, const int s) {
    if (static_cast<int>(f.size()) > s + 3 && f[s] == NOT && f[s + 1] == NOT && is_boolean(f[s + 2])) {
        f[s] = f[s + 2];
        erase_span(f, s + 1, 2);
        return true;
    }

    if (is_boolean(f[s]) && ensure_capacity(f, max_length, 2)) {
        const int a = f[s];
        f[s] = NOT;
        insert_values(f, s + 1, {NOT, a});
        return true;
    }

    return false;
}

/*
 * Simplify or introduce simple negations involving TRUE/FALSE constants.
 * - Contract: NOT TRUE -> FALSE, NOT FALSE -> TRUE
 * - Expand:  TRUE -> NOT FALSE, FALSE -> NOT TRUE (when capacity allows)
 */
bool is_negation(Formula& f, const int max_length, const int s) {
    if (static_cast<int>(f.size()) > s + 2 && f[s] == NOT) {
        if (f[s + 1] == TRUE_VALUE) {
            f[s] = FALSE_VALUE;
            erase_span(f, s + 1, 1);
            return true;
        }
        if (f[s + 1] == FALSE_VALUE) {
            f[s] = TRUE_VALUE;
            erase_span(f, s + 1, 1);
            return true;
        }
    }

    if (ensure_capacity(f, max_length, 1)) {
        if (f[s] == FALSE_VALUE) {
            f[s] = NOT;
            insert_values(f, s + 1, {TRUE_VALUE});
            return true;
        }
        if (f[s] == TRUE_VALUE) {
            f[s] = NOT;
            insert_values(f, s + 1, {FALSE_VALUE});
            return true;
        }
    }

    return false;
}

/*
 * Implements a small substitution mechanism used by the proof search to
 * introduce and later expand synthetic variable names that stand for
 * subexpressions. The function handles several cases:
 *
 * 1) Create a new variable alias for a NOT-expression:
 *      NOT a  ->  v  (and record v => NOT a)
 *    This introduces a fresh variable token and stores a SubExpression
 *    entry of kind=1 (NOT) with operand `a`.
 *
 * 2) Expand a stored NOT-alias back into NOT a when the map contains
 *    an entry for the current symbol with kind==1.
 *    This calls `decrement_variable_count` for the alias (no cascade)
 *    because the alias itself is being replaced by the underlying shape.
 *
 * 3) Create a new variable alias for a binary operator:
 *      OR a b  ->  v  (and record v => OR a b)
 *    This stores a SubExpression with kind set to the operator token
 *    and `a`, `b` set to the operands.
 *
 * 4) Expand a stored binary-alias back into its operator and operands
 *    when `variables_in_use` contains a matching record (kind >= 2).
 *    This expansion is guarded by `ensure_capacity`.
 */
bool is_substitution(Formula& f, const int max_length, const int s, VariableMap& variables_in_use) {
    std::unique_ptr<SubExpression> sub_expression;
    auto it = variables_in_use.find(f[s]);
    if (it != variables_in_use.end()) {
        sub_expression = std::make_unique<SubExpression>(it->second);
    }

    if (static_cast<int>(f.size()) > s + 2 && f[s] == NOT && is_boolean(f[s + 1])) {
        const int variable_name = new_random_variable_name(variables_in_use);
        variables_in_use[variable_name] = SubExpression{1, 1, f[s + 1], 0};
        f[s] = variable_name;
        erase_span(f, s + 1, 1);
        return true;
    }

    if (sub_expression != nullptr && sub_expression->kind == 1 && ensure_capacity(f, max_length, 1)) {
        decrement_variable_count(f[s], variables_in_use, false);
        f[s] = NOT;
        insert_values(f, s + 1, {sub_expression->a});
        return true;
    }

    if (static_cast<int>(f.size()) > s + 3 && (f[s] == OR || f[s] == AND) && is_boolean(f[s + 1]) && is_boolean(f[s + 2])) {
        const int variable_name = new_random_variable_name(variables_in_use);
        variables_in_use[variable_name] = SubExpression{1, f[s], f[s + 1], f[s + 2]};
        f[s] = variable_name;
        erase_span(f, s + 1, 2);
        return true;
    }

    if (sub_expression != nullptr && sub_expression->kind >= 2 && ensure_capacity(f, max_length, 2)) {
        const int kind = sub_expression->kind;
        const int a = sub_expression->a;
        const int b = sub_expression->b;
        decrement_variable_count(f[s], variables_in_use, false);
        f[s] = kind;
        insert_values(f, s + 1, {a, b});
        return true;
    }

    return false;
}

}

/*
 * Populate `variables_in_use` with initial counts for each variable token
 * appearing in `formula`.
 */
void store_initial_variables(const Formula& formula, VariableMap& variables_in_use) {
    variables_in_use.clear();
    for (const int symbol : formula) {
        if (symbol == STOP) {
            break;
        }
        increment_variable_count(symbol, variables_in_use);
    }
}

/*
 * Attempt to apply `law` at `index` within formula `f`.
 * Returns true if a rewrite was applied; false otherwise. The
 * `max_length` parameter bounds allowable expansions.
 */
bool transform_by_law_at_index(
    Formula& f,
    const int max_length,
    const int law,
    const int index,
    VariableMap& variables_in_use
) {
    const int f_stop = index_of_stop(f);
    if (f_stop < 0 || index < 0 || index >= f_stop) {
        return false;
    }

    switch (law) {
        case IDENTITY_OR:
            return is_identity_or(f, max_length, index);
        case IDENTITY_AND:
            return is_identity_and(f, max_length, index);
        case IDEMPOTENT_OR:
            return is_idempotent_or(f, max_length, index, variables_in_use);
        case IDEMPOTENT_AND:
            return is_idempotent_and(f, max_length, index, variables_in_use);
        case COMMUTATIVE_NEGATION:
            return is_commutative(f, index) || is_negation(f, max_length, index);
        case ASSOCIATIVE_DISTRIBUTIVE_DEMORGAN_DOUBLE_NEGATION:
            return is_associative(f, index) ||
                   is_distributive(f, max_length, index, variables_in_use) ||
                   is_demorgan(f, max_length, index) ||
                   is_double_negation(f, max_length, index);
        case COMPLEMENT:
            return is_complement(f, max_length, index, variables_in_use);
        case DOMINATION:
            return is_domination(f, max_length, index, variables_in_use);
        case ABSORPTION_OR:
            return is_absorption_or(f, max_length, index, variables_in_use);
        case ABSORPTION_AND:
            return is_absorption_and(f, max_length, index, variables_in_use);
        case SUBSTITUTION:
            return is_substitution(f, max_length, index, variables_in_use);
        default:
            return false;
    }
}

}
