import java.util.LinkedList;
import java.util.HashMap;
import java.util.Arrays;

// P11LFN (Prefix/Polish Notation, without Expressions, without Extras, with 11 Laws, (mostly) with Forms, Two-way, with Indices)

public class FormulaEnumeratorP11LFN {
    static final int MAXLENGTH = 100;

    // Special symbols
    static final int STOP = 0; // This indicates the end of a Boolean expression
    static final int NOT = 1;
    static final int OR = 2;
    static final int AND = 3;
    static final int FALSE = 4;
    static final int TRUE = 5;
    static final int minVariable = 6;

    // Laws of Boolean algebra
    static final int identityOR = 0; // a + 0 = a
    static final int identityAND = 1; // a * 1 = a
    static final int idempotentOR = 2; // a + a = a
    static final int idempotentAND = 3; // a * a = a
    static final int commutativeNegation = 4;
    // Commutative: a + b = b + a, a * b = b * a
    // Negation: -1 = 0, -0 = 1
    static final int associativeDistributiveDeMorganDoubleNegation = 5;
    // Associative: a + (b + c) = (a + b) + c, a * (b * c) = (a * b) * c
    // Distributive: a + (b * c) = (a + b) * (a + c), a * (b + c) = (a * b) + (a * c)
    // De Morgan: -(a + b) = -a * -b, -(a * b) = -a + -b
    // Double Negation: -(-a) = a
    static final int complement = 6; // a + -a = 1, a * -a = 0
    static final int domination = 7; // a + 1 = 1, a * 0 = 0
    static final int absorptionOR = 8; // a + (a * b) = a
    static final int absorptionAND = 9; // a * (a + b) = a
    static final int substitution = 10; // -a = x, a + b = x, a * b = x

    static final int lawCount = 11;
    static final String[] lawNames = new String[]{"identityOR", "identityAND", "idempotentOR", "idempotentAND", "commutative/negation", "associative/distributive/deMorgan/doubleNegation", "complement", "domination", "absorptionOR", "absorptionAND", "substitution"};

    public static void main(String[] args) {
        FormulaEnumeratorP11LFN enumerator = new FormulaEnumeratorP11LFN();
    }

    public FormulaEnumeratorP11LFN() {
        // These settings can be modified
        boolean findingTautologies = true; // false if finding contradictions
        int numberOfSymbolsInFormula = 3;
        int extraSpaceAfterFormulaInArray = 5;
        int searchProofUntilLength = 5;

        LinkedList<Integer>[] proofLengthHistogram = new LinkedList[searchProofUntilLength + 1];
        initializeHistogramBins(proofLengthHistogram, searchProofUntilLength);
        LinkedList<Integer>[] lawHistogram = new LinkedList[lawCount];
        initializeHistogramBins(lawHistogram, lawCount - 1);
        LinkedList<Integer>[] indexHistogram = new LinkedList[numberOfSymbolsInFormula + 1 + extraSpaceAfterFormulaInArray]; // + 1 for the STOP symbol
        initializeHistogramBins(indexHistogram, numberOfSymbolsInFormula + extraSpaceAfterFormulaInArray);

        long startTime = System.currentTimeMillis();
        enumerateBooleanFormulasOfSize(numberOfSymbolsInFormula, extraSpaceAfterFormulaInArray, findingTautologies, new int[MAXLENGTH], new int[MAXLENGTH], new boolean[MAXLENGTH], new LinkedList<>(), new HashMap<>(), searchProofUntilLength, new int[MAXLENGTH][2], new int[MAXLENGTH], new int[MAXLENGTH][2], proofLengthHistogram, lawHistogram, indexHistogram, new LinkedList<>());
        long finishTime = System.currentTimeMillis();
        System.out.println("RUNTIME: " + (finishTime - startTime) + " ms");
    }

    boolean isTruthValue(int symbol) {
        return symbol == TRUE || symbol == FALSE;
    }

    boolean isVariable(int symbol) {
        return symbol > 5;
    }

    boolean isBoolean(int symbol) {
        return symbol > 3;
    }

    int indexOfStop(int[] f, int fLength) {
        for (int i = 0; i < fLength; i++) {
            if (f[i] == STOP) {
                return i;
            }
        }
        return -1;
    }

    void storeInitialVariables(int[] formula, HashMap<Integer, int[]> variablesInUse) {
        variablesInUse.clear();
        int i = 0;
        while (formula[i] != STOP) {
            incrementVariableCount(formula[i], variablesInUse);
            i++;
        }
    }

    void incrementVariableCount(int variableName, HashMap<Integer, int[]> variablesInUse) {
        if (!isVariable(variableName)) {
            return;
        }
        int[] subExpression = variablesInUse.get(variableName);
        if (subExpression == null) {
            subExpression = new int[]{0, 0}; // {variable occurrence count, type of sub-expression}
            variablesInUse.put(variableName, subExpression);
        }
        subExpression[0]++;
        if (subExpression[1] >= 1) { // The sub-expression is -a
            incrementVariableCount(subExpression[2], variablesInUse); // 'a' in -a or a + b or a * b
            if (subExpression[1] >= 2) { // The sub-expression is a + b or a * b
                incrementVariableCount(subExpression[3], variablesInUse); // 'b' in a + b or a * b
            }
        }
    }

    void decrementVariableCount(int variableName, HashMap<Integer, int[]> variablesInUse, boolean cascading) {
        int[] subExpression = variablesInUse.get(variableName);
        if (subExpression == null) {
            return;
        }
        subExpression[0]--;
        if (cascading && subExpression[1] >= 1) { // The sub-expression is -a
            decrementVariableCount(subExpression[2], variablesInUse, true); // 'a' in -a or a + b or a * b
            if (subExpression[1] >= 2) { // The sub-expression is a + b or a * b
                decrementVariableCount(subExpression[3], variablesInUse, true); // 'b' in a + b or a * b
            }
        }
        if (subExpression[0] <= 0) { // Variable occurrence count is 0
            variablesInUse.remove(variableName);
        }
    }

    void shiftSuffixLeft(int[] f, int source, int destination, int fStop) {
        int i = source;
        int j = destination;
        while (i <= fStop) {
            f[j] = f[i];
            i++;
            j++;
        }
    }

    void shiftSuffixRight(int[] f, int source, int destination, int fStop) {
        int i = fStop;
        int j = fStop + destination - source;
        while (i >= source) {
            f[j] = f[i];
            i--;
            j--;
        }
    }

    void swap(int[] f, int i, int j) {
        int temp = f[i];
        f[i] = f[j];
        f[j] = temp;
    }

    boolean isIdentityOR(int[] f, int fLength, int fStop, int s) {
        // Infix: a + 0 = a
        // Polish: + a 0 = a
        if (fLength > s + 3
                && f[s] == OR && isBoolean(f[s + 1]) && f[s + 2] == FALSE) // a + 0
        {
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            return true;
        }
        // Infix: a = a + 0
        // Polish: a = + a 0
        else if (fLength > fStop + 2
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            f[s + 1] = f[s];
            f[s] = OR;
            f[s + 2] = FALSE;
            return true;
        }
        // No identity law in OR form detected
        return false;
    }

    boolean isIdentityAND(int[] f, int fLength, int fStop, int s) {
        // Infix: a * 1 = a
        // Polish: * a 1 = a
        if (fLength > s + 3
                && f[s] == AND && isBoolean(f[s + 1]) && f[s + 2] == TRUE) // a * 1
        {
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            return true;
        }
        // Infix: a = a * 1
        // Polish: a = * a 1
        else if (fLength > fStop + 2
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            f[s + 1] = f[s];
            f[s] = AND;
            f[s + 2] = TRUE;
            return true;
        }
        // No identity law in AND form detected
        return false;
    }

    boolean isIdempotentOR(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a + a = a
        // Polish: + a a = a
        if (fLength > s + 3
                && f[s] == OR && isBoolean(f[s + 1]) && f[s + 1] == f[s + 2]) // a + a
        {
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            decrementVariableCount(f[s], variablesInUse, true);
            return true;
        }
        // Infix: a = a + a
        // Polish: a = + a a
        else if (fLength > fStop + 2
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            incrementVariableCount(f[s], variablesInUse);
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            f[s + 1] = f[s];
            f[s + 2] = f[s];
            f[s] = OR;
            return true;
        }
        // No idempotent law in OR form detected
        return false;
    }

    boolean isIdempotentAND(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a * a = a
        // Polish: * a a = a
        if (fLength > s + 3
                && f[s] == AND && isBoolean(f[s + 1]) && f[s + 1] == f[s + 2]) // a * a
        {
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            decrementVariableCount(f[s], variablesInUse, true);
            return true;
        }
        // Infix: a = a * a
        // Polish: a = * a a
        else if (fLength > fStop + 2
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            incrementVariableCount(f[s], variablesInUse);
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            f[s + 1] = f[s];
            f[s + 2] = f[s];
            f[s] = AND;
            return true;
        }
        // No idempotent law in AND form detected
        return false;
    }

    boolean isCommutative(int[] f, int fLength, int s) {
        // Infix: a + b = b + a, a * b = b * a
        // Polish: + a b = + b a, * a b = * b a
        if (fLength > s + 3
                && (f[s] == OR || f[s] == AND) // OR or AND
                && isBoolean(f[s + 1]) && isBoolean(f[s + 2])) // 'a' and 'b' are Booleans
        {
            swap(f, s + 1, s + 2);
            return true;
        }
        // No commutative law detected
        return false;
    }

    boolean isAssociative(int[] f, int fLength, int s) {
        // Infix: a + (b + c) = (a + b) + c, a * (b * c) = (a * b) * c
        // Polish: + a + b c = + + a b c, * a * b c = * * a b c
        if (fLength > s + 5
                && (f[s] == OR || f[s] == AND) // First OR or AND
                && (isBoolean(f[s + 1]) || isBoolean(f[s + 2])) // Boolean 'a' at one of the two indices
                && (f[s + 1] == f[s] || f[s + 2] == f[s]) // Second OR or AND at one of the two indices
                && isBoolean(f[s + 3]) && isBoolean(f[s + 4])) // 'b' and 'c' are Booleans
        {
            swap(f, s + 1, s + 2);
            return true;
        }
        // No associative law detected
        return false;
    }

    boolean isDistributive(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a + (b * c) = (a + b) * (a + c), a * (b + c) = (a * b) + (a * c)
        // Polish: + a * b c = * + a b + a c, * a + b c = + * a b * a c
        if (fLength > fStop + 2
                && ((f[s] == OR && f[s + 2] == AND) || (f[s] == AND && f[s + 2] == OR)) // OR and AND
                && isBoolean(f[s + 1]) && isBoolean(f[s + 3]) && isBoolean(f[s + 4])) // 'a', 'b', and 'c' are Booleans
        {
            incrementVariableCount(f[s + 1], variablesInUse);
            shiftSuffixRight(f, s + 5, s + 7, fStop);
            f[s + 6] = f[s + 4]; // 'c'
            f[s + 5] = f[s + 1]; // 'a'
            f[s + 1] = f[s];
            f[s + 4] = f[s];
            f[s] = f[s + 2];
            f[s + 2] = f[s + 5]; // 'a'
            return true;
        }
        // Infix: (a + b) * (a + c) = a + (b * c), (a * b) + (a * c) = a * (b + c)
        // Polish: * + a b + a c = + a * b c, + * a b * a c = * a + b c
        else if (fLength > s + 7
                && ((f[s] == AND && f[s + 1] == OR && f[s + 4] == OR) || (f[s] == OR && f[s + 1] == AND && f[s + 4] == AND)) // AND and OR
                && isBoolean(f[s + 2]) && isBoolean(f[s + 3]) && isBoolean(f[s + 6]) // 'a', 'b', and 'c' are Booleans
                && f[s + 2] == f[s + 5]) // Second 'a'
        {
            f[s + 1] = f[s + 2]; // 'a'
            f[s + 2] = f[s];
            f[s] = f[s + 4];
            f[s + 4] = f[s + 6]; // 'c'
            shiftSuffixLeft(f, s + 7, s + 5, fStop);
            decrementVariableCount(f[s + 1], variablesInUse, true);
            return true;
        }
        // No distributive law detected
        return false;
    }

    boolean isDeMorgan(int[] f, int fLength, int fStop, int s) {
        // Infix: -(a + b) = -a * -b, -(a * b) = -a + -b
        // Polish: - + a b = * - a - b, - * a b = + - a - b
        if (fLength > fStop + 1
                && f[s] == NOT && isBoolean(f[s + 2]) && isBoolean(f[s + 3])) // -(a _ b)
        {
            if (f[s + 1] == OR) {
                shiftSuffixRight(f, s + 4, s + 5, fStop);
                f[s] = AND;
                f[s + 1] = NOT;
                f[s + 4] = f[s + 3]; // 'b'
                f[s + 3] = NOT;
                return true;
            } else if (f[s + 1] == AND) {
                shiftSuffixRight(f, s + 4, s + 5, fStop);
                f[s] = OR;
                f[s + 1] = NOT;
                f[s + 4] = f[s + 3]; // 'b'
                f[s + 3] = NOT;
                return true;
            }
        }
        // Infix: -a * -b = -(a + b), -a + -b = -(a * b)
        // Polish: * - a - b = - + a b, + - a - b = - * a b
        else if (fLength > s + 5
                && f[s + 1] == NOT && isBoolean(f[s + 2]) && f[s + 3] == NOT && isBoolean(f[s + 4])) // -a _ -b
        {
            if (f[s] == AND) {
                f[s + 1] = OR;
                f[s] = NOT;
                f[s + 3] = f[s + 4];
                shiftSuffixLeft(f, s + 5, s + 4, fStop);
                return true;
            } else if (f[s] == OR) {
                f[s + 1] = AND;
                f[s] = NOT;
                f[s + 3] = f[s + 4];
                shiftSuffixLeft(f, s + 5, s + 4, fStop);
                return true;
            }
        }
        // No De Morgan's law detected
        return false;
    }

    boolean isComplement(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a + -a = 1, a * -a = 0
        // Polish: + a - a = 1, * a - a = 0
        if (fLength > s + 4
                && isBoolean(f[s + 1]) && f[s + 2] == NOT && f[s + 1] == f[s + 3]) // a _ -a
        {
            if (f[s] == OR) {
                decrementVariableCount(f[s + 1], variablesInUse, true);
                decrementVariableCount(f[s + 1], variablesInUse, true);
                shiftSuffixLeft(f, s + 4, s + 1, fStop);
                f[s] = TRUE;
                return true;
            } else if (f[s] == AND) {
                decrementVariableCount(f[s + 1], variablesInUse, true);
                decrementVariableCount(f[s + 1], variablesInUse, true);
                shiftSuffixLeft(f, s + 4, s + 1, fStop);
                f[s] = FALSE;
                return true;
            }
        }
        // Infix: 1 = a + -a, 0 = a * -a
        // Polish: 1 = + a - a, 0 = * a - a
        else if (fLength > fStop + 3)
        {
            if (f[s] == TRUE) {
                shiftSuffixRight(f, s + 1, s + 4, fStop);
                f[s] = OR;
                f[s + 1] = TRUE; // 'a' can be any Boolean
                f[s + 2] = NOT;
                f[s + 3] = f[s + 1];
                //incrementVariableCount(f[s + 1], variablesInUse);
                //incrementVariableCount(f[s + 1], variablesInUse);
                return true;
            } else if (f[s] == FALSE) {
                shiftSuffixRight(f, s + 1, s + 4, fStop);
                f[s] = AND;
                f[s + 1] = TRUE; // 'a' can be any Boolean
                f[s + 2] = NOT;
                f[s + 3] = f[s + 1];
                //incrementVariableCount(f[s + 1], variablesInUse);
                //incrementVariableCount(f[s + 1], variablesInUse);
                return true;
            }
        }
        // No complement law detected
        return false;
    }

    boolean isDomination(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a + 1 = 1, a * 0 = 0
        // Polish: + a 1 = 1, * a 0 = 0
        if (fLength > s + 3
                && isBoolean(f[s + 1])) // a + 1
        {
            if (f[s] == OR && f[s + 2] == TRUE) {
                decrementVariableCount(f[s + 1], variablesInUse, true);
                f[s] = TRUE;
                shiftSuffixLeft(f, s + 3, s + 1, fStop);
                return true;
            } else if (f[s] == AND && f[s + 2] == FALSE) {
                decrementVariableCount(f[s + 1], variablesInUse, true);
                f[s] = FALSE;
                shiftSuffixLeft(f, s + 3, s + 1, fStop);
                return true;
            }
        }
        // Infix: 1 = a + 1, 0 = a * 0
        // Polish: 1 = + a 1, 0 = * a 0
        else if (fLength > fStop + 2)
        {
            if (f[s] == TRUE) {
                shiftSuffixRight(f, s + 1, s + 3, fStop);
                f[s] = OR;
                f[s + 1] = TRUE; // 'a'
                f[s + 2] = TRUE;
                //incrementVariableCount(f[s + 1], variablesInUse);
                return true;
            } else if (f[s] == FALSE) {
                shiftSuffixRight(f, s + 1, s + 3, fStop);
                f[s] = AND;
                f[s + 1] = FALSE; // 'a'
                f[s + 2] = FALSE;
                //incrementVariableCount(f[s + 1], variablesInUse);
                return true;
            }
        }
        // No domination law detected
        return false;
    }

    boolean isAbsorptionOR(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a + (a * b) = a
        // Polish: + a * a b = a
        if (fLength > s + 5
                && f[s] == OR && isBoolean(f[s + 1]) && f[s + 2] == AND && f[s + 1] == f[s + 3] && isBoolean(f[s + 4])) // a + (a * b)
        {
            decrementVariableCount(f[s + 1], variablesInUse, true);
            decrementVariableCount(f[s + 4], variablesInUse, true);
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 5, s + 1, fStop);
            return true;
        }
        // Infix: a = a + (a * b)
        // Polish: a = + a * a b
        else if (fLength > fStop + 5
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            shiftSuffixRight(f, s + 1, s + 5, fStop);
            f[s + 1] = f[s];
            f[s + 3] = f[s];
            f[s] = OR;
            f[s + 2] = AND;
            f[s + 4] = TRUE; // 'b'
            incrementVariableCount(f[s + 1], variablesInUse);
            //incrementVariableCount(f[s + 4], variablesInUse);
            return true;
        }
        // No absorption law in OR form detected
        return false;
    }

    boolean isAbsorptionAND(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        // Infix: a * (a + b) = a
        // Polish: * a + a b = a
        if (fLength > s + 5
                && f[s] == AND && isBoolean(f[s + 1]) && f[s + 2] == OR && f[s + 1] == f[s + 3] && isBoolean(f[s + 4])) // a * (a + b)
        {
            decrementVariableCount(f[s + 1], variablesInUse, true);
            decrementVariableCount(f[s + 4], variablesInUse, true);
            f[s] = f[s + 1];
            shiftSuffixLeft(f, s + 5, s + 1, fStop);
            return true;
        }
        // Infix: a = a * (a + b)
        // Polish: a = * a + a b
        else if (fLength > fStop + 5
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            shiftSuffixRight(f, s + 1, s + 5, fStop);
            f[s + 1] = f[s];
            f[s + 3] = f[s];
            f[s] = AND;
            f[s + 2] = OR;
            f[s + 4] = FALSE; // 'b'
            incrementVariableCount(f[s + 1], variablesInUse);
            //incrementVariableCount(f[s + 4], variablesInUse);
            return true;
        }
        // No absorption law in AND form detected
        return false;
    }

    boolean isDoubleNegation(int[] f, int fLength, int fStop, int s) {
        // Infix: -(-a) = a
        // Polish: - - a = a
        if (fLength > s + 3
                && f[s] == NOT && f[s + 1] == NOT && isBoolean(f[s + 2])) // -(-a)
        {
            f[s] = f[s + 2];
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            return true;
        }
        // Infix: a = -(-a)
        // Polish: a = - - a
        else if (fLength > fStop + 2
                && isBoolean(f[s])) // 'a' is a Boolean
        {
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            f[s + 2] = f[s];
            f[s] = NOT;
            f[s + 1] = NOT;
            return true;
        }
        // No double negation law detected
        return false;
    }

    boolean isNegation(int[] f, int fLength, int fStop, int s) {
        // Infix: -1 = 0, -0 = 1
        // Polish: - 1 = 0, - 0 = 1
        if (fLength > s + 2
                && f[s] == NOT)
        {
            if (f[s + 1] == TRUE) {
                f[s] = FALSE;
                shiftSuffixLeft(f, s + 2, s + 1, fStop);
                return true;
            } else if (f[s + 1] == FALSE) {
                f[s] = TRUE;
                shiftSuffixLeft(f, s + 2, s + 1, fStop);
                return true;
            }
        }
        // Infix: 0 = -1, 1 = -0
        // Polish: 0 = - 1, 1 = - 0
        else if (fLength > fStop + 1)
        {
            if (f[s] == FALSE) {
                shiftSuffixRight(f, s + 1, s + 2, fStop);
                f[s] = NOT;
                f[s + 1] = TRUE;
                return true;
            } else if (f[s] == TRUE) {
                shiftSuffixRight(f, s + 1, s + 2, fStop);
                f[s] = NOT;
                f[s + 1] = FALSE;
                return true;
            }
        }
        // No negation detected
        return false;
    }

    int newRandomVariableName(HashMap<Integer, int[]> variablesInUse) {
        int variableName;
        do {
            variableName = (int) (Math.random() * (Integer.MAX_VALUE - minVariable + 1)) + minVariable;
        } while (variablesInUse.containsKey(variableName));
        return variableName;
    }

    boolean isSubstitution(int[] f, int fLength, int fStop, int s, HashMap<Integer, int[]> variablesInUse) {
        int variableName;
        int[] subExpression = null;
        if (fLength > s + 1) {
            subExpression = variablesInUse.get(f[s]);
        }
        // Infix: -a = x
        // Polish: - a = x
        if (fLength > s + 2
                && f[s] == NOT && isBoolean(f[s + 1])) // -a
        {
            variableName = newRandomVariableName(variablesInUse);
            variablesInUse.put(variableName, new int[]{1, 1, f[s + 1]}); // {variable occurrence count, type of sub-expression, a}
            f[s] = variableName;
            shiftSuffixLeft(f, s + 2, s + 1, fStop);
            return true;
        }
        // Infix: x = -a
        // Polish: x = - a
        else if (fLength > fStop + 1
                && subExpression != null && subExpression[1] == 1) // 'x' is a pre-existing Boolean variable that represents the correct sub-expression
        {
            shiftSuffixRight(f, s + 1, s + 2, fStop);
            decrementVariableCount(f[s], variablesInUse, false);
            f[s] = NOT;
            f[s + 1] = subExpression[2]; // 'a'
            return true;
        }
        // Infix: a + b = x, a * b = x
        // Polish: + a b = x, * a b = x
        else if (fLength > s + 3
                && (f[s] == OR || f[s] == AND) // OR or AND
                && isBoolean(f[s + 1]) && isBoolean(f[s + 2])) // 'a' and 'b' are Booleans
        {
            variableName = newRandomVariableName(variablesInUse);
            variablesInUse.put(variableName, new int[]{1, f[s], f[s + 1], f[s + 2]}); // {variable occurrence count, type of sub-expression, a, b}
            f[s] = variableName;
            shiftSuffixLeft(f, s + 3, s + 1, fStop);
            return true;
        }
        // Infix: x = a + b, x = a * b
        // Polish: x = + a b, x = * a b
        else if (fLength > fStop + 2
                && subExpression != null && subExpression[1] >= 2) // 'x' is a pre-existing Boolean variable that represents the correct sub-expression
        {
            shiftSuffixRight(f, s + 1, s + 3, fStop);
            decrementVariableCount(f[s], variablesInUse, false);
            f[s] = subExpression[1]; // + or *
            f[s + 1] = subExpression[2]; // 'a'
            f[s + 2] = subExpression[3]; // 'b'
            return true;
        }
        // No substitution detected
        return false;
    }

    boolean isTransformationByLawAtIndex(int[] f, int fLength, int law, int index, HashMap<Integer, int[]> variablesInUse) {
        int fStop = indexOfStop(f, fLength);
        if (fStop < 0) {
            // There must be a STOP symbol at the end of a Boolean expression
            return false;
        }
        if (index < 0 || index >= fStop) {
            // The index must not be out of bounds
            return false;
        }
        switch (law) {
            case identityOR:
                return isIdentityOR(f, fLength, fStop, index);
            case identityAND:
                return isIdentityAND(f, fLength, fStop, index);
            case idempotentOR:
                return isIdempotentOR(f, fLength, fStop, index, variablesInUse);
            case idempotentAND:
                return isIdempotentAND(f, fLength, fStop, index, variablesInUse);
            case commutativeNegation:
                if (isCommutative(f, fLength, index)) {
                    return true;
                } else {
                    return isNegation(f, fLength, fStop, index);
                }
            case associativeDistributiveDeMorganDoubleNegation:
                if (isAssociative(f, fLength, index)) {
                    return true;
                } else if (isDistributive(f, fLength, fStop, index, variablesInUse)) {
                    return true;
                } else if (isDeMorgan(f, fLength, fStop, index)) {
                    return true;
                } else {
                    return isDoubleNegation(f, fLength, fStop, index);
                }
            case complement:
                return isComplement(f, fLength, fStop, index, variablesInUse);
            case domination:
                return isDomination(f, fLength, fStop, index, variablesInUse);
            case absorptionOR:
                return isAbsorptionOR(f, fLength, fStop, index, variablesInUse);
            case absorptionAND:
                return isAbsorptionAND(f, fLength, fStop, index, variablesInUse);
            case substitution:
                return isSubstitution(f, fLength, fStop, index, variablesInUse);
        }
        return false;
    }

    boolean isProofSequence(int[] formula, int[] editable, int fLength, int[][] sequence, int sequenceLength, int target, HashMap<Integer, int[]> variablesInUse) {
        int fStop = indexOfStop(formula, fLength);
        if (fStop < 1 || sequenceLength < 1 || (target != TRUE && target != FALSE)) {
            // The Boolean formula array and editable array must have the same length, the Boolean expression or sequence length must be at least 1, and the target must be a truth value
            return false;
        }
        storeInitialVariables(formula, variablesInUse);
        System.arraycopy(formula, 0, editable, 0, fStop + 1);
        for (int i = 0; i < sequenceLength; i++) {
            if (!isTransformationByLawAtIndex(editable, fLength, sequence[i][0], sequence[i][1], variablesInUse)) {
                return false;
            } else if (editable[0] == target && editable[1] == STOP) {
                return true;
            }
        }
        return false;
    }

    void initializeHistogramBins(LinkedList<Integer>[] histogramBins, int maxBinIndex) {
        for (int i = 0; i <= maxBinIndex; i++) {
            histogramBins[i] = new LinkedList<>();
        }
    }

    void fillBeforeStop(int element, int[] f, int fStop) {
        for (int i = 0; i < fStop; i++) {
            f[i] = element;
        }
    }

    void resetProofSequence(int[][] proofSequence, int m) {
        for (int i = 0; i < m; i++) {
            proofSequence[i][0] = 0;
            proofSequence[i][1] = 0;
        }
    }

    int countVariables(int[] f, int fStop, boolean[] variableChecklist) {
        int i;
        // Clear checklist
        for (i = 0; i < fStop; i++) {
            variableChecklist[i] = false;
        }
        // Fill checklist while counting variables
        int variableCount = 0;
        int variable;
        for (i = 0; i < fStop; i++) {
            variable = f[i] - minVariable;
            if (variable >= 0 && !variableChecklist[variable]) {
                // New variable found
                variableChecklist[variable] = true;
                variableCount++;
            }
        }
        // Find missing variables
        boolean previous = variableChecklist[0];
        for (i = 1; i < fStop; i++) {
            if (!previous && variableChecklist[i]) {
                // Gap found
                return -1;
            }
            previous = variableChecklist[i];
        }
        return variableCount;
    }

    boolean isValidSyntax(int[] f, int fStop, LinkedList<Integer> operandStack) {
        int symbol;
        // Read from right to left
        for (int i = fStop - 1; i >= 0; i--) {
            symbol = f[i];
            if (symbol == NOT) {
                if (operandStack.isEmpty()) {
                    return false;
                } else {
                    operandStack.removeFirst();
                }
                operandStack.addFirst(0);
            } else if (symbol == OR || symbol == AND) {
                if (operandStack.isEmpty()) {
                    return false;
                } else {
                    operandStack.removeFirst();
                }
                if (operandStack.isEmpty()) {
                    return false;
                } else {
                    operandStack.removeFirst();
                }
                operandStack.addFirst(0);
            } else {
                // The symbol is an operand
                operandStack.addFirst(0);
            }
        }
        if (operandStack.isEmpty()) {
            return false;
        }
        operandStack.removeFirst();
        if (!operandStack.isEmpty()) {
            operandStack.clear();
            return false;
        }
        return true;
    }

    boolean isSatisfyingAssignment(int[] f, int fStop, LinkedList<Integer> operandStack, long assignmentBits) {
        int symbol, leftOperand, rightOperand;
        // Read from right to left
        for (int i = fStop - 1; i >= 0; i--) {
            symbol = f[i];
            if (symbol == NOT) {
                leftOperand = operandStack.removeFirst();
                if (
                        leftOperand == TRUE
                                || (leftOperand >= minVariable && ((assignmentBits & (1L << (leftOperand - minVariable))) != 0))
                ) {
                    operandStack.addFirst(FALSE);
                } else {
                    operandStack.addFirst(TRUE);
                }
            } else if (symbol == OR) {
                rightOperand = operandStack.removeFirst();
                leftOperand = operandStack.removeFirst();
                if (
                        leftOperand == TRUE || rightOperand == TRUE
                                || (leftOperand >= minVariable && ((assignmentBits & (1L << (leftOperand - minVariable))) != 0))
                                || (rightOperand >= minVariable && ((assignmentBits & (1L << (rightOperand - minVariable))) != 0))
                ) {
                    operandStack.addFirst(TRUE);
                } else {
                    operandStack.addFirst(FALSE);
                }
            } else if (symbol == AND) {
                rightOperand = operandStack.removeFirst();
                leftOperand = operandStack.removeFirst();
                if (
                        leftOperand == FALSE || rightOperand == FALSE
                                || (leftOperand >= minVariable && ((assignmentBits & (1L << (leftOperand - minVariable))) == 0))
                                || (rightOperand >= minVariable && ((assignmentBits & (1L << (rightOperand - minVariable))) == 0))
                ) {
                    operandStack.addFirst(FALSE);
                } else {
                    operandStack.addFirst(TRUE);
                }
            } else {
                // The symbol is an operand
                operandStack.addFirst(symbol);
            }
        }
        return operandStack.removeFirst() == TRUE;
    }

    void printBooleanFormula(int[] f, int fStop) {
        int i, symbol;
        System.out.print("{");
        for (i = 0; i < fStop; i++) {
            System.out.print(f[i]);
            if (i + 1 < fStop) {
                System.out.print(", ");
            }
        }
        System.out.print("} = [");
        for (i = 0; i < fStop; i++) {
            symbol = f[i];
            if (symbol == NOT) {
                System.out.print("-");
            } else if (symbol == OR) {
                System.out.print("+");
            } else if (symbol == AND) {
                System.out.print("*");
            } else if (symbol == FALSE) {
                System.out.print("F");
            } else if (symbol == TRUE) {
                System.out.print("T");
            } else {
                System.out.print("x" + (symbol - minVariable));
            }
            if (i + 1 < fStop) {
                System.out.print(" ");
            }
        }
        System.out.print("]");
    }

    boolean isTautologyOrContradiction(boolean tautOrCon, int[] f, int fStop, int variableCount, LinkedList<Integer> operandStack, int tautOrConIndex) {
        // tautOrCon == true means tautology, tautOrCon == false means unsatisfiable
        long limit = 1L << variableCount;
        boolean satisfying;
        for (long assignmentBits = 0; assignmentBits < limit; assignmentBits++) {
            satisfying = isSatisfyingAssignment(f, fStop, operandStack, assignmentBits);
            if ((tautOrCon && !satisfying) || (!tautOrCon && satisfying)) {
                printBooleanFormula(f, fStop);
                if (tautOrCon) {
                    System.out.print(" is not a tautology.");
                } else {
                    System.out.print(" is not a contradiction.");
                }
                if (variableCount > 0) {
                    System.out.print(" Proof: ");
                }
                int bit = 1;
                for (int i = 0; i < variableCount; i++) {
                    System.out.print("x" + i + " = ");
                    if ((assignmentBits & bit) == 0) {
                        System.out.print(false);
                    } else {
                        System.out.print(true);
                    }
                    if (i + 1 < variableCount) {
                        System.out.print(", ");
                    }
                    bit = bit << 1;
                }
                System.out.println();
                return false;
            }
        }
        System.out.print("#" + tautOrConIndex + ": ");
        printBooleanFormula(f, fStop);
        if (tautOrCon) {
            System.out.print(" is a tautology.");
        } else {
            System.out.print(" is a contradiction.");
        }
        return true;
    }

    void printProofSequence(int[][] proofSequence, int sequenceLength) {
        int i;
        System.out.print("{");
        for (i = 0; i < sequenceLength; i++) {
            System.out.print("{" + proofSequence[i][0] + ", " + proofSequence[i][1] + "}");
            if (i + 1 < sequenceLength) {
                System.out.print(", ");
            }
        }
        System.out.print("} = [");
        for (i = 0; i < sequenceLength; i++) {
            System.out.print(lawNames[proofSequence[i][0]] + " at " + proofSequence[i][1]);
            if (i + 1 < sequenceLength) {
                System.out.print(", ");
            }
        }
        System.out.print("]");
    }

    boolean bruteForceTautologyOrContradictionProofsOfSize(int m, int target, int[] f, int[] editable, int fLength, HashMap<Integer, int[]> variablesInUse, int[][] proofSequence) {
        int mMinus1 = m - 1;
        int lastLaw = lawCount - 1;
        int lastIndexInF = fLength - 1;
        resetProofSequence(proofSequence, m);
        int i = 0;
        int j;
        while (i >= 0) {
            if (isProofSequence(f, editable, fLength, proofSequence, m, target, variablesInUse)) {
                return true;
            }
            // Increment
            i = mMinus1;
            j = 0; // Skip j = 1 because proofSequence[m - 1][1] must be 0
            proofSequence[i][j]++;
            while (i >= 0 && ((j == 0 && proofSequence[i][0] > lastLaw) || (j == 1 && proofSequence[i][1] > lastIndexInF) || (i == mMinus1 && j == 0 && proofSequence[i][0] >= substitution))) { // The last step must not be substitution
                // Reset symbol
                proofSequence[i][j] = 0;
                // Next symbol
                j--;
                if (j < 0) {
                    i--;
                    j = 1;
                }
                if (i >= 0) {
                    proofSequence[i][j]++;
                }
            }
        }
        // No proof of length m found
        return false;
    }

    int bruteForceTautologyOrContradictionProofsUntilSize(int maxM, int target, int[] f, int[] editable, int fLength, HashMap<Integer, int[]> variablesInUse, int[][] proofSequence) {
        for (int m = 1; m <= maxM; m++) {
            if (bruteForceTautologyOrContradictionProofsOfSize(m, target, f, editable, fLength, variablesInUse, proofSequence)) {
                System.out.print(" Proof of length " + m + ": ");
                printProofSequence(proofSequence, m);
                System.out.println();
                return m;
            }
        }
        System.out.println(" No proof found");
        return -1;
    }

    void copyProofSequence(int[][] proofSequence, int[][] copy, int sequenceLength) {
        for (int i = 0; i < sequenceLength; i++) {
            copy[i][0] = proofSequence[i][0];
            copy[i][1] = proofSequence[i][1];
        }
    }

    void countOccurrencesInProof(int[][] proofSequence, int sequenceLength, int inTuple, LinkedList<Integer>[] histogram, int tautOrConIndex) {
        int lawOrIndex;
        for (int i = 0; i < sequenceLength; i++) {
            lawOrIndex = proofSequence[i][inTuple];
            histogram[lawOrIndex].add(tautOrConIndex);
        }
    }

    void printHistogramBin(LinkedList<Integer> histogramBin) {
        for (int item : histogramBin) {
            System.out.print("#" + item + ", ");
        }
        System.out.println();
    }

    int sortHistogram(LinkedList<Integer>[] histogram, int maxBinIndex, int[][] sequence) {
        int histogramBinFrequency;
        int pairCount = 0;
        // Collect in reverse order so that the ranking in descending order is a stable sorting
        for (int i = maxBinIndex; i >= 0; i--) {
            histogramBinFrequency = histogram[i].size();
            if (histogramBinFrequency > 0) {
                sequence[pairCount][0] = i;
                sequence[pairCount][1] = histogramBinFrequency;
                pairCount++;
            }
        }
        // Sort by frequency
        Arrays.sort(sequence, 0, pairCount, (o1, o2) -> Integer.compare(o1[1], o2[1]));
        return pairCount;
    }

    void printHoldoutList(LinkedList<int[]> holdoutList, int fStop) {
        int i = 0;
        for (int[] formula : holdoutList) {
            System.out.print(i + ": ");
            printBooleanFormula(formula, fStop);
            System.out.println();
            i++;
        }
    }

    void enumerateBooleanFormulasOfSize(int n, int padding, boolean tautOrCon, int[] f, int[] editable, boolean[] variableChecklist, LinkedList<Integer> operandStack, HashMap<Integer, int[]> variablesInUse, int proofSearchLimit, int[][] sequence, int[] formulaWithLongestProof, int[][] longestProof, LinkedList<Integer>[] proofLengthHistogram, LinkedList<Integer>[] lawHistogram, LinkedList<Integer>[] indexHistogram, LinkedList<int[]> holdoutList) {
        // n symbols excluding the STOP symbol
        // tautOrCon == true means finding tautologies, tautOrCon == false means finding contradictions
        if (n < 2) {
            System.out.println("n should not be less than 2.");
            return;
        }
        if (padding < 0) {
            System.out.println("The padding must not be negative.");
            return;
        }
        int fLength = n + 1 + padding; // + 1 for the STOP symbol
        fillBeforeStop(1, f, n);
        f[n] = STOP;
        int target = TRUE; // Finding tautologies
        if (!tautOrCon) {
            target = FALSE; // Finding contradictions
        }

        int nMinus1 = n - 1;
        int maxSymbol = n + minVariable - 1;
        int variableCount;
        operandStack.clear();
        int validSyntaxAndLabelingCount = 0;
        int tautologyOrUnsatisfiableFormulaCount = 0;
        formulaWithLongestProof[n] = STOP;
        int maxProofLength = 0;
        int holdoutCount = 0;
        int i, proofLength;
        while (f[0] <= 3) { // The first symbol can only be an operator
            variableCount = countVariables(f, n, variableChecklist);
            if (variableCount >= 0 && isValidSyntax(f, n, operandStack)) {
                validSyntaxAndLabelingCount++;
                if (isTautologyOrContradiction(tautOrCon, f, n, variableCount, operandStack, tautologyOrUnsatisfiableFormulaCount)) {
                    int[] formulaCopy = new int[fLength];
                    System.arraycopy(f, 0, formulaCopy, 0, n + 1);
                    // Attempt to find a proof sequence
                    proofLength = bruteForceTautologyOrContradictionProofsUntilSize(proofSearchLimit, target, f, editable, fLength, variablesInUse, sequence);
                    if (proofLength > maxProofLength) {
                        System.arraycopy(f, 0, formulaWithLongestProof, 0, n);
                        copyProofSequence(sequence, longestProof, proofLength);
                        maxProofLength = proofLength;
                    }
                    if (proofLength > 0) {
                        proofLengthHistogram[proofLength].add(tautologyOrUnsatisfiableFormulaCount);
                        countOccurrencesInProof(sequence, proofLength, 0, lawHistogram, tautologyOrUnsatisfiableFormulaCount);
                        countOccurrencesInProof(sequence, proofLength, 1, indexHistogram, tautologyOrUnsatisfiableFormulaCount);
                    } else {
                        holdoutCount++;
                        holdoutList.add(formulaCopy);
                    }
                    tautologyOrUnsatisfiableFormulaCount++;
                }
            }
            // Increment
            i = nMinus1;
            f[i]++;
            while (f[i] > maxSymbol && i > 0) {
                // Reset symbol
                f[i] = 1;
                // Next index
                i--;
                f[i]++;
            }
        }
        System.out.print("\nThere are " + validSyntaxAndLabelingCount + " Boolean formulas with " + n + " symbols and with valid syntax and variable labeling." +
                "\n\nThere are " + tautologyOrUnsatisfiableFormulaCount);
        if (tautOrCon) {
            System.out.println(" tautologies with " + n + " symbols.\n");
        } else {
            System.out.println(" contradictions with " + n + " symbols.\n");
        }
        System.out.print("Boolean formula with the longest proof: ");
        printBooleanFormula(formulaWithLongestProof, n);
        System.out.print("\nLongest proof: ");
        printProofSequence(longestProof, maxProofLength);
        System.out.println("\nMax proof length = " + maxProofLength + "\n\nProof Length Histogram:\n");
        int frequencyCount;
        for (i = 1; i <= proofSearchLimit; i++) {
            frequencyCount = proofLengthHistogram[i].size(); // Frequency of proof length
            if (tautOrCon) {
                System.out.print("\t" + frequencyCount + " tautologies have a minimal proof length of " + i);
            } else {
                System.out.print("\t" + frequencyCount + " contradictions have a minimal proof length of " + i);
            }
            if (frequencyCount > 0) {
                System.out.print(":\n\t");
                printHistogramBin(proofLengthHistogram[i]);
            } else {
                System.out.println();
            }
            System.out.println();
        }
        System.out.println("Most common to least common minimal proof lengths (with non-zero frequency):");
        frequencyCount = sortHistogram(proofLengthHistogram, proofSearchLimit, sequence);
        for (i = frequencyCount - 1; i >= 0; i--) {
            System.out.print(sequence[i][0]);
            if (i > 0) {
                System.out.print(", ");
            }
        }
        System.out.println("\n\nHistogram of Boolean Algebra Law Occurrences:\n");
        for (i = 0; i < lawCount; i++) {
            frequencyCount = lawHistogram[i].size(); // Frequency of Boolean algebra law
            System.out.print("\tThe " + lawNames[i] + " law occurred " + frequencyCount + " times");
            if (frequencyCount > 0) {
                System.out.print(" in the minimal proofs of the following Boolean formulas:\n\t");
                printHistogramBin(lawHistogram[i]);
            } else {
                System.out.println();
            }
            System.out.println();
        }
        System.out.println("Most common to least common Boolean algebra laws (with non-zero frequency):");
        frequencyCount = sortHistogram(lawHistogram, lawCount - 1, sequence);
        for (i = frequencyCount - 1; i >= 0; i--) {
            System.out.print(lawNames[sequence[i][0]]);
            if (i > 0) {
                System.out.print(", ");
            }
        }
        System.out.println("\n\nHistogram of Proof Steps per Boolean Formula Index:\n");
        for (i = 0; i < fLength; i++) {
            frequencyCount = indexHistogram[i].size(); // Frequency of Boolean formula index
            System.out.print("\t" + frequencyCount + " proof steps occurred at Boolean formula index " + i);
            if (frequencyCount > 0) {
                System.out.print(" in the minimal proofs of the following Boolean formulas:\n\t");
                printHistogramBin(indexHistogram[i]);
            } else {
                System.out.println();
            }
            System.out.println();
        }
        System.out.println("Most common to least common Boolean formula indices (with non-zero frequency):");
        frequencyCount = sortHistogram(indexHistogram, fLength - 1, sequence);
        for (i = frequencyCount - 1; i >= 0; i--) {
            System.out.print(sequence[i][0]);
            if (i > 0) {
                System.out.print(", ");
            }
        }
        System.out.println("\n");
        if (holdoutCount > 0) {
            System.out.println(holdoutCount + " holdouts have a minimal proof length exceeding " + proofSearchLimit + ":");
            printHoldoutList(holdoutList, n);
            System.out.println();
        }
    }
}
