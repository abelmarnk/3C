#include <iostream>

// Code for converting a 3-CNF Boolean formula to Polish notation

const int MAXLENGTH = 100;

// Special symbols
const int STOP = 0; // This indicates the end of a Boolean expression
const int NOT = 1;
const int OR = 2;
const int AND = 3;
const int FALSE = 4;
const int TRUE = 5;
const int minVariable = 6;

int convert3CNFtoPolishNotation(int CNF[MAXLENGTH][3], int clauseCount, int polishNotation[], int padding) {
    if (padding < 0) {
        std::cout << "The padding must not be negative.\n";
        return -1;
    }
    if (clauseCount < 1) {
        std::cout << "The 3-CNF formula must have at least one clause.\n";
        return -1;
    }
    // Predict the length of the Boolean formula in Polish notation
    int literalCount = clauseCount * 3;
    int symbolCount = literalCount; // For counting symbols that will be in the Polish notation formula
    int i, j, literal;
    for (i = 0; i < clauseCount; i++) {
        for (j = 0; j < 3; j++) {
            literal = CNF[i][j];
            if (literal == 0 || std::abs(literal) > literalCount) {
                std::cout << "Literal " << j << " in clause " << i << " must be non-zero and not out of range.\n";
                return -1;
            }
            if (literal < 0) {
                // Count NOT symbol
                symbolCount++;
            }
        }
    }
    symbolCount += 2 * clauseCount; // Count OR symbols
    symbolCount += clauseCount - 1; // Count AND symbols
    symbolCount++; // Count the STOP symbol at the end
    int fLength = symbolCount + padding; // Make room after the STOP symbol
    // Fill the Boolean formula in Polish notation
    int symbol = 0;
    int maxClause = clauseCount - 1;
    for (i = 0; i < clauseCount; i++) {
        if (i < maxClause && clauseCount > 1) {
            polishNotation[symbol] = AND;
            symbol++;
        }
        polishNotation[symbol] = OR;
        symbol++;
        for (j = 0; j < 3; j++) {
            literal = CNF[i][j];
            if (literal < 0) {
                polishNotation[symbol] = NOT;
                symbol++;
                polishNotation[symbol] = minVariable - literal - 1;
                symbol++;
            } else {
                polishNotation[symbol] = minVariable + literal - 1;
                symbol++;
            }
            if (j == 0) {
                polishNotation[symbol] = OR;
                symbol++;
            }
        }
    }
    polishNotation[symbol] = STOP;
    // Print the Boolean formula in Polish notation
    symbolCount = symbol + 1;
    for (i = 0; i < symbolCount; i++) {
        symbol = polishNotation[i];
        if (symbol == NOT) {
            std::cout << "- ";
        } else if (symbol == OR) {
            std::cout << "+ ";
        } else if (symbol == AND) {
            std::cout << "* ";
        } else if (symbol == STOP) {
            std::cout << "STOP\n";
        } else {
            std::cout << "x" << (symbol - minVariable) << " ";
        }
    }
    return fLength;
}

int main() {
    int exampleCNF[MAXLENGTH][3] = {
        {1, -3, 4}, 
        {-2, 3, -5}, 
        {-1, 4, -5}, 
        {2, -4, 6}
    };

    int polishNotation[MAXLENGTH];
    int extraSpaceAfterFormulaInArray = 5;
    convert3CNFtoPolishNotation(exampleCNF, 4, polishNotation, extraSpaceAfterFormulaInArray);
}
