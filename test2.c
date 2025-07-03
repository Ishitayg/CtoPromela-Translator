// Test for enhanced C-to-Promela translator
// Including float, double, char support

// Test basic variable declarations
int a;
float b;
double c;
char d;

// Test variable declarations with initialization
int e = 5;
float f = 3.14;
double g = 2.71828;
char h = 'X';

// Test function with int return type and parameters of different types
int calculate(int x, float y, double z, char op) {
    if (op == '+') {
        printf("Adding %d and %f\n", x, y);
        return x + y + z;  // Note: This will be approximated in Promela
    } else if (op == '*') {
        printf("Multiplying %d and %f\n", x, y);
        return x * y * z;  // Note: This will be approximated in Promela
    } else {
        printf("Unknown operation: %c\n", op);
        return 0;
    }
}

// Test function with float return type
float get_pi() {
    return 3.14159;  // Note: This will be approximated in Promela
}

// Test function with char return type
char get_grade(int score) {
    if (score >= 90) {
        return 'A';
    } else if (score >= 80) {
        return 'B';
    } else if (score >= 70) {
        return 'C';
    } else if (score >= 60) {
        return 'D';
    } else {
        return 'F';
    }
}

// Main function to test everything
int main() {
    // Initialize variables with values
    a = 10;
    b = 20.5;
    c = 30.75;
    d = 'Z';
    
    // Test if-else with character comparison
    if (d == 'Z') {
        printf("d is Z\n");
    } else {
        printf("d is not Z\n");
    }
    
    // Test function calls
    int result = calculate(a, b, c, '+');
    printf("Result of calculation: %d\n", result);
    
    // Test float function
    float pi = get_pi();
    printf("Value of pi: %f\n", pi);
    
    // Test char function
    char grade = get_grade(85);
    printf("Grade: %c\n", grade);
    
    return 0;
}