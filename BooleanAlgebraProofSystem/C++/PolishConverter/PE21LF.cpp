#include <iostream>
#include <unordered_map>

// PE21LF (Prefix/Polish Notation, with Expressions, without Extras, with 21 Laws, with Forms, Two-way, without Indices)

class Tuple {
    public:
        int law;
        int* formula;
        Tuple(int tupleLaw, int tupleFormula[]) {
            law = tupleLaw;
            formula = tupleFormula;
        }
};

// Special symbols
const int STOP = 0; // This indicates the end of a Boolean expression
const int NOT = 1;
const int OR = 2;
const int AND = 3;
const int FALSE = 4;
const int TRUE = 5;

// Laws of Boolean algebra
const int identityOR = 0; // a + 0 = a
const int identityAND = 1; // a * 1 = a
const int idempotentOR = 2; // a + a = a
const int idempotentAND = 3; // a * a = a
const int commutativeOR = 4; // a + b = b + a
const int commutativeAND = 5; // a * b = b * a
const int associativeOR = 6; // a + (b + c) = (a + b) + c
const int associativeAND = 7; // a * (b * c) = (a * b) * c
const int distributiveOR = 8; // a + (b * c) = (a + b) * (a + c)
const int distributiveAND = 9; // a * (b + c) = (a * b) + (a * c)
const int deMorganOR = 10; // -(a + b) = -a * -b
const int deMorganAND = 11; // -(a * b) = -a + -b
const int complementOR = 12; // a + -a = 1
const int complementAND = 13; // a * -a = 0
const int dominationOR = 14; // a + 1 = 1
const int dominationAND = 15; // a * 0 = 0
const int absorptionOR = 16; // a + (a * b) = a
const int absorptionAND = 17; // a * (a + b) = a
const int doubleNegation = 18; // -(-a) = a
const int negation = 19; // -1 = 0, -0 = 1
const int substitution = 20; // -a = x, a + b = x, a * b = x

bool isTruthValue(int symbol) {
    return symbol == TRUE || symbol == FALSE;
}

bool isVariable(int symbol) {
    return symbol > 5;
}

bool isBoolean(int symbol) {
    return symbol > 3;
}

int firstDissimilarity(int f[], int g[], int fLength) {
    for (int i = 0; i < fLength; i++) {
        if (f[i] == STOP || g[i] == STOP) {
            // STOP must not be before a dissimilarity
            return -1;
        }
        if (f[i] != g[i]) {
            // The index where both expressions first differ
            return i;
        }
    }
    // Reached the end, so both are identical
    return -1;
}

int indexOfStop(int f[], int fLength) {
    for (int i = 0; i < fLength; i++) {
        if (f[i] == STOP) {
            return i;
        }
    }
    return -1;
}

bool sameSuffix(int f[], int g[], int fLength, int fStop, int gStop, int s, int suffixAtF, int suffixAtG, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    if (computedSuffixMatrix[suffixAtF][suffixAtG]) {
        // Reuse computed Boolean
        return sameSuffixMatrix[suffixAtF][suffixAtG];
    }
    // Keep track of the pair of suffix indices
    computedSuffixMatrix[suffixAtF][suffixAtG] = true;
    computedSuffixList[*computedSuffixCount][0] = suffixAtF;
    computedSuffixList[*computedSuffixCount][1] = suffixAtG;
    (*computedSuffixCount)++;
    // Preemptively set the result to false
    sameSuffixMatrix[suffixAtF][suffixAtG] = false;
    // Compare the suffix of both Boolean expressions
    int i = s + suffixAtF;
    int j = s + suffixAtG;
    if (i >= fLength || j >= fLength) {
        // A suffix must be within a Boolean expression
        return false;
    }
    int difference = suffixAtF - suffixAtG;
    if ((difference >= 0 && gStop + difference != fStop) || (difference < 0 && fStop + (suffixAtG - suffixAtF) != gStop)) {
        // The ends of both expressions do not correspond correctly
        return false;
    }
    while (i < fStop && j < gStop) {
        if (f[i] != g[j]) {
            // There are extra changes after the first changed parts of the expressions
            return false;
        }
        i++;
        j++;
    }
    // The first changed parts of the expressions are the only changed parts
    sameSuffixMatrix[suffixAtF][suffixAtG] = true;
    return true;
}

// The only 14 pairs of suffix indices that need to be checked:
// sameSuffixMatrix[1][2]
// sameSuffixMatrix[1][3]
// sameSuffixMatrix[1][4]
// sameSuffixMatrix[1][5]
// sameSuffixMatrix[2][1]
// sameSuffixMatrix[2][2]
// sameSuffixMatrix[3][1]
// sameSuffixMatrix[4][1]
// sameSuffixMatrix[4][4]
// sameSuffixMatrix[4][5]
// sameSuffixMatrix[5][1]
// sameSuffixMatrix[5][4]
// sameSuffixMatrix[5][7]
// sameSuffixMatrix[7][5]

void resetSuffixes(bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    int suffixAtF, suffixAtG;
    while (*computedSuffixCount > 0) {
        (*computedSuffixCount)--;
        suffixAtF = computedSuffixList[*computedSuffixCount][0];
        suffixAtG = computedSuffixList[*computedSuffixCount][1];
        computedSuffixMatrix[suffixAtF][suffixAtG] = false;
    }
}

void incrementVariableCount(int variableName, std::unordered_map<int, int*> variablesInUse) {
    if (!isVariable(variableName)) {
        return;
    }
    int* subExpression = variablesInUse[variableName];
    if (subExpression == NULL) {
        subExpression = new int[2]{0, 0}; // {variable occurrence count, type of sub-expression}
        variablesInUse[variableName] = subExpression;
    }
    subExpression[0]++;
    if (subExpression[1] >= 1) { // The sub-expression is -a
        incrementVariableCount(subExpression[2], variablesInUse); // 'a' in -a or a + b or a * b
        if (subExpression[1] >= 2) { // The sub-expression is a + b or a * b
            incrementVariableCount(subExpression[3], variablesInUse); // 'b' in a + b or a * b
        }
    }
}

void decrementVariableCount(int variableName, std::unordered_map<int, int*> variablesInUse, bool cascading) {
    int* subExpression = variablesInUse[variableName];
    if (subExpression == NULL) {
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
        delete[] subExpression;
        subExpression = nullptr;
        variablesInUse.erase(variableName);
    }
}

void storeInitialVariables(int formula[], std::unordered_map<int, int*> variablesInUse) {
    variablesInUse.clear();
    int i = 0;
    while (formula[i] != STOP) {
        incrementVariableCount(formula[i], variablesInUse);
        i++;
    }
}

bool isIdentityOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: a + 0 = a
    // Polish: + a 0 = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) && f[s + 2] == FALSE // a + 0 = _
        && g[s] == f[s + 1]) // _ = a
    {
        return true;
    }
    // Infix: a = a + 0
    // Polish: a = + a 0
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && isBoolean(g[s + 1]) && g[s + 2] == FALSE // _ = a + 0
        && f[s] == g[s + 1]) // a = _
    {
        return true;
    }
    // No identity law in OR form detected
    return false;
}

bool isIdentityAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: a * 1 = a
    // Polish: * a 1 = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) && f[s + 2] == TRUE // a * 1 = _
        && g[s] == f[s + 1]) // _ = a
    {
        return true;
    }
    // Infix: a = a * 1
    // Polish: a = * a 1
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && isBoolean(g[s + 1]) && g[s + 2] == TRUE // _ = a * 1
        && f[s] == g[s + 1]) // a = _
    {
        return true;
    }
    // No identity law in AND form detected
    return false;
}

bool isIdempotentOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a + a = a
    // Polish: + a a = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 1] == f[s + 2] // Both operands are 'a' in the previous expression
        && g[s] == f[s + 1]) // The changed part in the next expression is 'a'
    {
        decrementVariableCount(g[s], variablesInUse, true);
        return true;
    }
    // Infix: a = a + a
    // Polish: a = + a a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 1] == g[s + 2] // Both operands are 'a' in the next expression
        && f[s] == g[s + 1]) // The changed part in the previous expression is 'a'
    {
        incrementVariableCount(f[s], variablesInUse);
        return true;
    }
    // No idempotent law in OR form detected
    return false;
}

bool isIdempotentAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a * a = a
    // Polish: * a a = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 1] == f[s + 2] // Both operands are 'a' in the previous expression
        && g[s] == f[s + 1]) // The changed part in the next expression is 'a'
    {
        decrementVariableCount(g[s], variablesInUse, true);
        return true;
    }
    // Infix: a = a * a
    // Polish: a = * a a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 1] == g[s + 2] // Both operands are 'a' in the next expression
        && f[s] == g[s + 1]) // The changed part in the previous expression is 'a'
    {
        incrementVariableCount(f[s], variablesInUse);
        return true;
    }
    // No idempotent law in AND form detected
    return false;
}

bool isCommutativeOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    if (s < 1) {
        // Not enough room to step back
        return false;
    }
    // Infix: a + b = b + a
    // Polish: + a b = + b a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 2, 2, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s - 1] == OR // OR in the previous expression
        && g[s - 1] == OR // OR in the next expression
        && isBoolean(f[s]) && isBoolean(f[s + 1]) // 'a' and 'b' are Booleans
        && f[s] == g[s + 1] && f[s + 1] == g[s]) // 'a' and 'b' are swapped
    {
        return true;
    }
    // No commutative law in OR form detected
    return false;
}

bool isCommutativeAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    if (s < 1) {
        // Not enough room to step back
        return false;
    }
    // Infix: a * b = b * a
    // Polish: * a b = * b a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 2, 2, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s - 1] == AND // AND in the previous expression
        && g[s - 1] == AND // AND in the next expression
        && isBoolean(f[s]) && isBoolean(f[s + 1]) // 'a' and 'b' are Booleans
        && f[s] == g[s + 1] && f[s + 1] == g[s]) // 'a' and 'b' are swapped
    {
        return true;
    }
    // No commutative law in AND form detected
    return false;
}

bool isAssociativeOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    if (s < 1) {
        // Not enough room to step back
        return false;
    }
    // Infix: a + (b + c) = (a + b) + c
    // Polish: + a + b c = + + a b c
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s - 1] == OR // First OR in the previous expression
        && g[s - 1] == OR // First OR in the next expression
        && isBoolean(f[s]) // 'a' is a Boolean
        && f[s + 1] == OR // Second OR in the previous expression
        && isBoolean(f[s + 2]) && isBoolean(f[s + 3]) // 'b' and 'c' are Booleans
        && f[s] == g[s + 1] && g[s] == OR // 'a' and OR are swapped
        && f[s + 2] == g[s + 2] && f[s + 3] == g[s + 3]) // 'b' and 'c' are not swapped
    {
        return true;
    }
    // Infix: (a + b) + c = a + (b + c)
    // Polish: + + a b c = + a + b c
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s - 1] == OR // First OR in the next expression
        && f[s - 1] == OR // First OR in the previous expression
        && isBoolean(g[s]) // 'a' is a Boolean
        && g[s + 1] == OR // Second OR in the next expression
        && isBoolean(g[s + 2]) && isBoolean(g[s + 3]) // 'b' and 'c' are Booleans
        && g[s] == f[s + 1] && f[s] == OR // 'a' and OR are swapped
        && g[s + 2] == f[s + 2] && g[s + 3] == f[s + 3]) // 'b' and 'c' are not swapped
    {
        return true;
    }
    // No associative law in OR form detected
    return false;
}

bool isAssociativeAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    if (s < 1) {
        // Not enough room to step back
        return false;
    }
    // Infix: a * (b * c) = (a * b) * c
    // Polish: * a * b c = * * a b c
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s - 1] == AND // First AND in the previous expression
        && g[s - 1] == AND // First AND in the next expression
        && isBoolean(f[s]) // 'a' is a Boolean
        && f[s + 1] == AND // Second AND in the previous expression
        && isBoolean(f[s + 2]) && isBoolean(f[s + 3]) // 'b' and 'c' are Booleans
        && f[s] == g[s + 1] && g[s] == AND // 'a' and AND are swapped
        && f[s + 2] == g[s + 2] && f[s + 3] == g[s + 3]) // 'b' and 'c' are not swapped
    {
        return true;
    }
    // Infix: (a * b) * c = a * (b * c)
    // Polish: * * a b c = * a * b c
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s - 1] == AND // First AND in the next expression
        && f[s - 1] == AND // First AND in the previous expression
        && isBoolean(g[s]) // 'a' is a Boolean
        && g[s + 1] == AND // Second AND in the next expression
        && isBoolean(g[s + 2]) && isBoolean(g[s + 3]) // 'b' and 'c' are Booleans
        && g[s] == f[s + 1] && f[s] == AND // 'a' and AND are swapped
        && g[s + 2] == f[s + 2] && g[s + 3] == f[s + 3]) // 'b' and 'c' are not swapped
    {
        return true;
    }
    // No associative law in AND form detected
    return false;
}

bool isDistributiveOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a + (b * c) = (a + b) * (a + c)
    // Polish: + a * b c = * + a b + a c
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 7, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && f[s + 2] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && isBoolean(f[s + 3]) && isBoolean(f[s + 4]) // 'b' and 'c' are Booleans
        && g[s] == AND // AND in the next expression
        && g[s + 1] == OR // First OR in the next expression
        && g[s + 4] == OR // Second OR in the next expression
        && f[s + 1] == g[s + 2] && f[s + 3] == g[s + 3] && f[s + 1] == g[s + 5] && f[s + 4] == g[s + 6]) // _ = (a + b) * (a + c)
    {
        incrementVariableCount(f[s + 1], variablesInUse);
        return true;
    }
    // Infix: (a + b) * (a + c) = a + (b * c)
    // Polish: * + a b + a c = + a * b c
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 7, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && g[s + 2] == AND // AND in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && isBoolean(g[s + 3]) && isBoolean(g[s + 4]) // 'b' and 'c' are Booleans
        && f[s] == AND // AND in the previous expression
        && f[s + 1] == OR // First OR in the previous expression
        && f[s + 4] == OR // Second OR in the previous expression
        && g[s + 1] == f[s + 2] && g[s + 3] == f[s + 3] && g[s + 1] == f[s + 5] && g[s + 4] == f[s + 6]) // (a + b) * (a + c) = _
    {
        decrementVariableCount(g[s + 1], variablesInUse, true);
        return true;
    }
    // No distributive law in OR form detected
    return false;
}

bool isDistributiveAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a * (b + c) = (a * b) + (a * c)
    // Polish: * a + b c = + * a b * a c
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 7, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && f[s + 2] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && isBoolean(f[s + 3]) && isBoolean(f[s + 4]) // 'b' and 'c' are Booleans
        && g[s] == OR // OR in the next expression
        && g[s + 1] == AND // First AND in the next expression
        && g[s + 4] == AND // Second AND in the next expression
        && f[s + 1] == g[s + 2] && f[s + 3] == g[s + 3] && f[s + 1] == g[s + 5] && f[s + 4] == g[s + 6]) // _ = (a * b) + (a * c)
    {
        incrementVariableCount(f[s + 1], variablesInUse);
        return true;
    }
    // Infix: (a * b) + (a * c) = a * (b + c)
    // Polish: + * a b * a c = * a + b c
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 7, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && g[s + 2] == OR // OR in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && isBoolean(g[s + 3]) && isBoolean(g[s + 4]) // 'b' and 'c' are Booleans
        && f[s] == OR // OR in the previous expression
        && f[s + 1] == AND // First AND in the previous expression
        && f[s + 4] == AND // Second AND in the previous expression
        && g[s + 1] == f[s + 2] && g[s + 3] == f[s + 3] && g[s + 1] == f[s + 5] && g[s + 4] == f[s + 6]) // (a * b) + (a * c) = _
    {
        decrementVariableCount(g[s + 1], variablesInUse, true);
        return true;
    }
    // No distributive law in AND form detected
    return false;
}

bool isDeMorganOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: -(a + b) = -a * -b
    // Polish: - + a b = * - a - b
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == NOT // NOT in the previous expression
        && f[s + 1] == OR // OR in the previous expression
        && g[s] == AND // AND in the next expression
        && isBoolean(f[s + 2]) && isBoolean(f[s + 3]) // 'a' and 'b' are Booleans
        && g[s + 1] == NOT && f[s + 2] == g[s + 2] // -a
        && g[s + 3] == NOT && f[s + 3] == g[s + 4]) // -b
    {
        return true;
    }
    // Infix: -a * -b = -(a + b)
    // Polish: * - a - b = - + a b
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == NOT // NOT in the next expression
        && g[s + 1] == OR // OR in the next expression
        && f[s] == AND // AND in the previous expression
        && isBoolean(g[s + 2]) && isBoolean(g[s + 3]) // 'a' and 'b' are Booleans
        && f[s + 1] == NOT && g[s + 2] == f[s + 2] // -a
        && f[s + 3] == NOT && g[s + 3] == f[s + 4]) // -b
    {
        return true;
    }
    // No De Morgan's law in OR form detected
    return false;
}

bool isDeMorganAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: -(a * b) = -a + -b
    // Polish: - * a b = + - a - b
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == NOT // NOT in the previous expression
        && f[s + 1] == AND // AND in the previous expression
        && g[s] == OR // OR in the next expression
        && isBoolean(f[s + 2]) && isBoolean(f[s + 3]) // 'a' and 'b' are Booleans
        && g[s + 1] == NOT && f[s + 2] == g[s + 2] // -a
        && g[s + 3] == NOT && f[s + 3] == g[s + 4]) // -b
    {
        return true;
    }
    // Infix: -a + -b = -(a * b)
    // Polish: + - a - b = - * a b
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == NOT // NOT in the next expression
        && g[s + 1] == AND // AND in the next expression
        && f[s] == OR // OR in the previous expression
        && isBoolean(g[s + 2]) && isBoolean(g[s + 3]) // 'a' and 'b' are Booleans
        && f[s + 1] == NOT && g[s + 2] == f[s + 2] // -a
        && f[s + 3] == NOT && g[s + 3] == f[s + 4]) // -b
    {
        return true;
    }
    // No De Morgan's law in AND form detected
    return false;
}

bool isComplementOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a + -a = 1
    // Polish: + a - a = 1
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 2] == NOT // NOT in the previous expression
        && f[s + 1] == f[s + 3] // -a
        && g[s] == TRUE) // TRUE in the next expression
    {
        decrementVariableCount(f[s + 1], variablesInUse, true);
        decrementVariableCount(f[s + 1], variablesInUse, true);
        return true;
    }
    // Infix: 1 = a + -a
    // Polish: 1 = + a - a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 2] == NOT // NOT in the next expression
        && g[s + 1] == g[s + 3] // -a
        && f[s] == TRUE) // TRUE in the previous expression
    {
        incrementVariableCount(g[s + 1], variablesInUse);
        incrementVariableCount(g[s + 1], variablesInUse);
        return true;
    }
    // No complement law in OR form detected
    return false;
}

bool isComplementAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a * -a = 0
    // Polish: * a - a = 0
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 4, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 2] == NOT // NOT in the previous expression
        && f[s + 1] == f[s + 3] // -a
        && g[s] == FALSE) // FALSE in the next expression
    {
        decrementVariableCount(f[s + 1], variablesInUse, true);
        decrementVariableCount(f[s + 1], variablesInUse, true);
        return true;
    }
    // Infix: 0 = a * -a
    // Polish: 0 = * a - a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 4, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 2] == NOT // NOT in the next expression
        && g[s + 1] == g[s + 3] // -a
        && f[s] == FALSE) // FALSE in the previous expression
    {
        incrementVariableCount(g[s + 1], variablesInUse);
        incrementVariableCount(g[s + 1], variablesInUse);
        return true;
    }
    // No complement law in AND form detected
    return false;
}

bool isDominationOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a + 1 = 1
    // Polish: + a 1 = 1
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 2] == TRUE // TRUE in the previous expression
        && g[s] == TRUE) // TRUE in the next expression
    {
        decrementVariableCount(f[s + 1], variablesInUse, true);
        return true;
    }
    // Infix: 1 = a + 1
    // Polish: 1 = + a 1
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 2] == TRUE // TRUE in the next expression
        && f[s] == TRUE) // TRUE in the previous expression
    {
        incrementVariableCount(g[s + 1], variablesInUse);
        return true;
    }
    // No domination law in OR form detected
    return false;
}

bool isDominationAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a * 0 = 0
    // Polish: * a 0 = 0
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 2] == FALSE // FALSE in the previous expression
        && g[s] == FALSE) // FALSE in the next expression
    {
        decrementVariableCount(f[s + 1], variablesInUse, true);
        return true;
    }
    // Infix: 0 = a * 0
    // Polish: 0 = * a 0
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 2] == FALSE // FALSE in the next expression
        && f[s] == FALSE) // FALSE in the previous expression
    {
        incrementVariableCount(g[s + 1], variablesInUse);
        return true;
    }
    // No domination law in AND form detected
    return false;
}

bool isAbsorptionOR(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a + (a * b) = a
    // Polish: + a * a b = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == OR // OR in the previous expression
        && f[s + 2] == AND // AND in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 1] == f[s + 3] // Second 'a' in the previous expression
        && isBoolean(f[s + 4]) // 'b' is a Boolean
        && g[s] == f[s + 1]) // The changed part in the next expression is 'a'
    {
        decrementVariableCount(g[s], variablesInUse, true);
        decrementVariableCount(f[s + 4], variablesInUse, true);
        return true;
    }
    // Infix: a = a + (a * b)
    // Polish: a = + a * a b
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == OR // OR in the next expression
        && g[s + 2] == AND // AND in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 1] == g[s + 3] // Second 'a' in the next expression
        && isBoolean(g[s + 4]) // 'b' is a Boolean
        && f[s] == g[s + 1]) // The changed part in the previous expression is 'a'
    {
        incrementVariableCount(f[s], variablesInUse);
        incrementVariableCount(g[s + 4], variablesInUse);
        return true;
    }
    // No absorption law in OR form detected
    return false;
}

bool isAbsorptionAND(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: a * (a + b) = a
    // Polish: * a + a b = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 5, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == AND // AND in the previous expression
        && f[s + 2] == OR // OR in the previous expression
        && isBoolean(f[s + 1]) // 'a' is a Boolean
        && f[s + 1] == f[s + 3] // Second 'a' in the previous expression
        && isBoolean(f[s + 4]) // 'b' is a Boolean
        && g[s] == f[s + 1]) // The changed part in the next expression is 'a'
    {
        decrementVariableCount(g[s], variablesInUse, true);
        decrementVariableCount(f[s + 4], variablesInUse, true);
        return true;
    }
    // Infix: a = a * (a + b)
    // Polish: a = * a + a b
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 5, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == AND // AND in the next expression
        && g[s + 2] == OR // OR in the next expression
        && isBoolean(g[s + 1]) // 'a' is a Boolean
        && g[s + 1] == g[s + 3] // Second 'a' in the next expression
        && isBoolean(g[s + 4]) // 'b' is a Boolean
        && f[s] == g[s + 1]) // The changed part in the previous expression is 'a'
    {
        incrementVariableCount(f[s], variablesInUse);
        incrementVariableCount(g[s + 4], variablesInUse);
        return true;
    }
    // No absorption law in AND form detected
    return false;
}

bool isDoubleNegation(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: -(-a) = a
    // Polish: - - a = a
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == NOT // First NOT in the previous expression
        && f[s + 1] == NOT // Second NOT in the previous expression
        && isBoolean(f[s + 2]) // 'a' is a Boolean
        && g[s] == f[s + 2]) // The changed part in the next expression is just 'a'
    {
        return true;
    }
    // Infix: a = -(-a)
    // Polish: a = - - a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == NOT // First NOT in the next expression
        && g[s + 1] == NOT // Second NOT in the next expression
        && isBoolean(g[s + 2]) // 'a' is a Boolean
        && f[s] == g[s + 2]) // The changed part in the previous expression is just 'a'
    {
        return true;
    }
    // No double negation law detected
    return false;
}

bool isNegation(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount) {
    // Infix: -1 = 0, -0 = 1
    // Polish: - 1 = 0, - 0 = 1
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 2, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == NOT // NOT in the previous expression
        && ((f[s + 1] == TRUE && g[s] == FALSE) // -1 = 0
            || (f[s + 1] == FALSE && g[s] == TRUE))) // -0 = 1
    {
        return true;
    }
    // Infix: 0 = -1, 1 = -0
    // Polish: 0 = - 1, 1 = - 0
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 2, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == NOT // NOT in the next expression
        && ((g[s + 1] == TRUE && f[s] == FALSE) // 0 = -1
            || (g[s + 1] == FALSE && f[s] == TRUE))) // 1 = -0
    {
        return true;
    }
    // No negation detected
    return false;
}

bool isSubstitution(int f[], int g[], int fLength, int fStop, int gStop, int s, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    // Infix: -a = x
    // Polish: - a = x
    if (sameSuffix(f, g, fLength, fStop, gStop, s, 2, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && f[s] == NOT && isBoolean(f[s + 1]) // -a = _
        && isVariable(g[s]) && !variablesInUse.count(g[s])) // 'x' is a new Boolean variable
    {
        variablesInUse[g[s]] = new int[3]{1, 1, f[s + 1]}; // {variable occurrence count, type of sub-expression, a}
        return true;
    }
    // Infix: x = -a
    // Polish: x = - a
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 2, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && g[s] == NOT && isBoolean(g[s + 1]) // _ = -a
        && variablesInUse.count(f[s]) // 'x' is a pre-existing Boolean variable
        && variablesInUse[f[s]][1] == 1 && variablesInUse[f[s]][2] == g[s + 1]) // 'x' represents the correct sub-expression
    {
        decrementVariableCount(f[s], variablesInUse, false);
        return true;
    }
    // Infix: a + b = x, a * b = x
    // Polish: + a b = x, * a b = x
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 3, 1, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && (f[s] == OR || f[s] == AND) // OR or AND in the previous expression
        && isBoolean(f[s + 1]) && isBoolean(f[s + 2]) // 'a' and 'b' are Booleans
        && isVariable(g[s]) && !variablesInUse.count(g[s])) // 'x' is a new Boolean variable
    {
        variablesInUse[g[s]] = new int[4]{1, f[s], f[s + 1], f[s + 2]}; // {variable occurrence count, type of sub-expression, a, b}
        return true;
    }
    // Infix: x = a + b, x = a * b
    // Polish: x = + a b, x = * a b
    else if (sameSuffix(f, g, fLength, fStop, gStop, s, 1, 3, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount)
        && (g[s] == OR || g[s] == AND) // OR or AND in the next expression
        && isBoolean(g[s + 1]) && isBoolean(g[s + 2]) // _ = a + b, _ = a * b
        && variablesInUse.count(f[s]) // 'x' is a pre-existing Boolean variable
        && variablesInUse[f[s]][1] == g[s] && variablesInUse[f[s]][2] == g[s + 1] && variablesInUse[f[s]][3] == g[s + 2]) // 'x' represents the correct sub-expression
    {
        decrementVariableCount(f[s], variablesInUse, false);
        return true;
    }
    // No substitution detected
    return false;
}

bool isTransformationByLaw(int f[], int g[], int fLength, int law, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    int s = firstDissimilarity(f, g, fLength);
    if (s < 0) {
        // Both Boolean expressions must differ somewhere
        return false;
    }
    int fStop = indexOfStop(f, fLength);
    int gStop = indexOfStop(g, fLength);
    if (fStop < 0 || gStop < 0) {
        // There must be a STOP symbol at the end of a Boolean expression
        return false;
    }
    switch (law) {
    case identityOR:
        return isIdentityOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case identityAND:
        return isIdentityAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case idempotentOR:
        return isIdempotentOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case idempotentAND:
        return isIdempotentAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case commutativeOR:
        return isCommutativeOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case commutativeAND:
        return isCommutativeAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case associativeOR:
        return isAssociativeOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case associativeAND:
        return isAssociativeAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case distributiveOR:
        return isDistributiveOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case distributiveAND:
        return isDistributiveAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case deMorganOR:
        return isDeMorganOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case deMorganAND:
        return isDeMorganAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case complementOR:
        return isComplementOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case complementAND:
        return isComplementAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case dominationOR:
        return isDominationOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case dominationAND:
        return isDominationAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case absorptionOR:
        return isAbsorptionOR(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case absorptionAND:
        return isAbsorptionAND(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    case doubleNegation:
        return isDoubleNegation(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case negation:
        return isNegation(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    case substitution:
        return isSubstitution(f, g, fLength, fStop, gStop, s, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse);
    }
    return false;
}

bool isProofSequence(int formula[], int fLength, Tuple sequence[], int sequenceLength, int target, bool sameSuffixMatrix[8][8], bool computedSuffixMatrix[8][8], int computedSuffixList[14][2], int* computedSuffixCount, std::unordered_map<int, int*> variablesInUse) {
    if (indexOfStop(formula, fLength) < 1 || sequenceLength < 1 || (target != TRUE && target != FALSE)) {
        // The Boolean expression or sequence length must be at least 1, and the target must be a truth value
        return false;
    }
    storeInitialVariables(formula, variablesInUse);
    resetSuffixes(computedSuffixMatrix, computedSuffixList, computedSuffixCount);
    if (!isTransformationByLaw(formula, sequence[0].formula, fLength, sequence[0].law, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse)) {
        return false;
    } else if (sequence[0].formula[0] == target && sequence[0].formula[1] == STOP) {
        return true;
    }
    int lastTupleIndex = sequenceLength - 1;
    for (int i = 0; i < lastTupleIndex; i++) {
        resetSuffixes(computedSuffixMatrix, computedSuffixList, computedSuffixCount);
        if (!isTransformationByLaw(sequence[i].formula, sequence[i + 1].formula, fLength, sequence[i + 1].law, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, computedSuffixCount, variablesInUse)) {
            return false;
        } else if (sequence[i + 1].formula[0] == target && sequence[i + 1].formula[1] == STOP) {
            return true;
        }
    }
    return false;
}

int main() {
    // Boolean matrix for suffix matching
    bool sameSuffixMatrix[8][8] = {0};
    bool computedSuffixMatrix[8][8] = {0};
    int computedSuffixList[14][2] = {0};
    int computedSuffixCount = 0;
    // Hash map to store variables
    std::unordered_map<int, int*> variablesInUse = {};

    // Example transformation
    int exampleF[] = {6, NOT, NOT, 7, STOP};
    int exampleG[] = {6, 7, STOP, 0, 0};
    storeInitialVariables(exampleF, variablesInUse);
    std::cout << "Example transformation is ";
    if (isTransformationByLaw(exampleF, exampleG, 5, doubleNegation, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, &computedSuffixCount, variablesInUse)) {
        std::cout << "correct\n";
    } else {
        std::cout << "NOT correct\n";
    }

    // Example sequence
    int exampleFormula[] = {AND, 7, AND, 6, NOT, 6, STOP};
    int tuple1Formula[] = {AND, 7, FALSE, STOP, 0, 0, 0};
    int tuple2Formula[] = {FALSE, STOP, 0, 0, 0, 0, 0};
    Tuple exampleSequence[] = {
        Tuple(complementAND, tuple1Formula),
        Tuple(dominationAND, tuple2Formula)
    };
    std::cout << "Example sequence is ";
    if (isProofSequence(exampleFormula, 7, exampleSequence, 2, FALSE, sameSuffixMatrix, computedSuffixMatrix, computedSuffixList, &computedSuffixCount, variablesInUse)) {
        std::cout << "correct\n";
    } else {
        std::cout << "NOT correct\n";
    }
}
