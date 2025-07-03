C to Promela Translator
=======================

Overview
--------
This project converts C programs into Promela code. Promela is a modeling language used for verifying 
concurrent programs with the SPIN model checker.

Purpose
-------
The goal is to:
- Translate C programs into Promela
- Verify the C program for deadlocks, race conditions, and other issues
- Bridge the gap between C programming and formal verification

Tools Used
----------
- Lex (Flex) for lexical analysis
- Yacc (Bison) for parsing and syntax analysis

How It Works
------------
1. Lex reads the C code and breaks it into tokens.
2. Yacc parses the tokens and builds an Abstract Syntax Tree (AST).
3. A code generator walks through the AST and creates equivalent Promela code.

Translation Features
--------------------
- Basic data types:
  - int → int
  - char → byte
  - float/double → approximated as int
- C constructs supported:
  - Variable declarations
  - Function definitions and calls
  - if/else, while loops, for loops
  - switch-case, break, continue
  - return statements (simulated using global variables)
  - printf statements

Limitations
-----------
- Complex C features like pointers and dynamic memory (malloc, free) are not supported
- Structures and arrays with pointers are limited
- Some C behavior may not be exactly preserved

How to Use
----------
1. Compile the translator using a Makefile or build script.
2. Run the translator with a C source file:
   ./translator file.c
3. The tool will generate a Promela (.pml) file.
4. Use the SPIN model checker to verify the generated Promela code.

Building and Running the Translator
----------------------------------
Step 1: Generate the parser from the grammar file
  C:\win_flex_bison-2.5.25\bison.exe -d parser.y

Step 2: Generate the lexer from the flex specification
  C:\win_flex_bison-2.5.25\flex.exe -o lexer.c lexer.l

Step 3: Compile the translator
  g++ -o translator lexer.c parser.tab.c -I. -std=c++11 -D_GNU_SOURCE

Step 4: Run the translator to convert C code to Promela
  cmd /c "translator.exe < test.c > test.pml"

Example
-------
Input: C code with functions, loops, and conditionals
Output: Promela code with proctype blocks and Promela-style control flow

Note
----
This is a basic translator for educational use and may not handle all edge cases of the C language.
