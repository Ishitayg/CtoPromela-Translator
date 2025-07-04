/* filepath: c:\Desktop\PPP Project\lexer.l */
%{
#include <string>
#include <cstring>  // Added for string functions
#include <cstdlib>  // Added for atoi
#include "ast.h"    // Add this line to include AST definitions
#include "parser.tab.h"  // Will be generated by Yacc/Bison

// Import the custom strdup implementation from parser.y
extern char* my_strdup(const char* s);

// Function to handle errors
void lexical_error(const char *message);

// For string literals
std::string string_buffer;

// Initialize line counter
int line_counter = 1;

// For recognizing special return variables
bool is_return_var(const char* name) {
    return (strcmp(name, "calc_result") == 0 ||
            strcmp(name, "pi_value") == 0 ||
            strcmp(name, "grade_value") == 0);
}
%}

/* Lexer options */
%option noyywrap
%option yylineno
%option nounput
%option noinput
%option nodefault

/* Regular expression definitions */
DIGIT       [0-9]
ID          [a-zA-Z_][a-zA-Z0-9_]*
WHITESPACE  [ \t\r]

/* States */
%x STRING_STATE
%x COMMENT_STATE

%%

 /* Keywords */
"int"       { return INT; }
"float"     { return FLOAT; }
"double"    { return DOUBLE; }
"char"      { return CHAR; }
"if"        { return IF; }
"else"      { return ELSE; }
"while"     { return WHILE; }
"return"    { return RETURN; }
"printf"    { return PRINTF; }
"chan"      { return CHAN; }  /* Add this line for channel keyword */
"of"        { return OF; }    /* Add this line for 'of' keyword */

 /* Operators */
"="         { return '='; }
"+"         { return '+'; }
"-"         { return '-'; }
"*"         { return '*'; }
"/"         { return '/'; }
"%"         { return '%'; }
"=="        { return EQ; }
"!="        { return NE; }
"<"         { return '<'; }
">"         { return '>'; }
"<="        { return LE; }
">="        { return GE; }
"&&"        { return AND; }
"||"        { return OR; }
"!"         { return '!'; }

 /* Punctuation */
";"         { return ';'; }
"("         { return '('; }
")"         { return ')'; }
"{"         { return '{'; }
"}"         { return '}'; }
","         { return ','; }
"["         { return '['; }  /* Add this line for opening bracket */
"]"         { return ']'; }  /* Add this line for closing bracket */
"?"         { return '?'; }   /* Add this for channel receive operations */

 /* String literals for printf */
\"          { 
    string_buffer.clear();
    BEGIN(STRING_STATE); 
}

<STRING_STATE>\"  { 
    yylval.str = my_strdup(string_buffer.c_str());
    BEGIN(INITIAL);
    return STRING_LITERAL;
}

<STRING_STATE>\\n { string_buffer += "\\n"; }
<STRING_STATE>\\t { string_buffer += "\\t"; }
<STRING_STATE>\\\" { string_buffer += "\""; }
<STRING_STATE>\\  { string_buffer += "\\"; }
<STRING_STATE>[^\\\"\n]+ { string_buffer += yytext; }

 /* Handle newlines in string literals - BEFORE EOF rule */
<STRING_STATE>\n { 
    lexical_error("Newline in string literal"); 
    string_buffer += "\\n"; 
    yylineno++; 
}

 /* Handle EOF in string state */
<STRING_STATE><<EOF>> { 
    lexical_error("Unterminated string literal"); 
    string_buffer.clear();
    BEGIN(INITIAL);
    yylval.str = my_strdup("");
    return STRING_LITERAL;
}

 /* Numbers and identifiers */
{DIGIT}+    {
              yylval.num = atoi(yytext);
              return NUMBER;
            }

{ID}        {
              yylval.id = my_strdup(yytext);
              return IDENTIFIER;
            }

 /* Character literals */
\'[^\']\' { 
    yylval.chr = yytext[1]; 
    return CHAR_VAL; 
}

\'\\n\'  { 
    yylval.chr = '\n'; 
    return CHAR_VAL; 
}

\'\\t\'  { 
    yylval.chr = '\t'; 
    return CHAR_VAL; 
}

\'\\\'\'  { 
    yylval.chr = '\''; 
    return CHAR_VAL; 
}

\'\\\\\'  { 
    yylval.chr = '\\'; 
    return CHAR_VAL; 
}

 /* Float literals */
{DIGIT}+\.{DIGIT}+ {
    yylval.dval = atof(yytext);
    return FLOAT_VAL;
}

 /* Handle newlines explicitly */
\n          { yylineno++; }

 /* Skip whitespace - now doesn't include \n */
{WHITESPACE}+ { /* ignore */ }

 /* Comments */
"//".*      { /* ignore single-line comments */ }
"/*"        {
              BEGIN(COMMENT_STATE);
            }
<COMMENT_STATE>"*/" { BEGIN(INITIAL); }
<COMMENT_STATE>[^\n*]+ { /* ignore comment content */ }
<COMMENT_STATE>\n    { yylineno++; }
<COMMENT_STATE>"*"   { /* ignore asterisks */ }

 /* Handle EOF in comment state */
<COMMENT_STATE><<EOF>> { 
    lexical_error("Unterminated comment"); 
    BEGIN(INITIAL); 
}

 /* Error handling */
.           { lexical_error("Unrecognized character"); }

%%

void lexical_error(const char *message) {
  fprintf(stderr, "Error at line %d: %s - '%s'\n", yylineno, message, yytext);
}