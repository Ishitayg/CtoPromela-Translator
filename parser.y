/* filepath: c:\Desktop\PPP Project\parser.y */
%code requires {
    // This code will be included at the top of parser.tab.h
    #include "ast.h"
}

%{
#include <iostream>
#include <string>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cstring>  // For string functions
#include <sstream>  // For stringstream
#include "ast.h"    // Include the AST header

// Global root node for the AST
ProgramNode* root = nullptr;
// Current function name for return statements
std::string current_function_name;
// Store function return types for generating global variables
std::vector<std::pair<std::string, std::string>> function_returns;

// Custom strdup implementation to avoid linking issues
char* my_strdup(const char* s) {
    if (s == nullptr) return nullptr;
    size_t len = strlen(s) + 1;
    char* new_str = (char*)malloc(len);
    if (new_str) {
        memcpy(new_str, s, len);
    }
    return new_str;
}

extern int yylex();
extern int yylineno;
extern char* yytext;
void yyerror(const char* s);

// For tracking indentation level
int indent_level = 0;
std::string get_indent() {
    std::string indent = "";
    for (int i = 0; i < indent_level; i++) {
        indent += "  ";
    }
    return indent;
}

// Memory tracking for cleanup
std::vector<ASTNode*> all_nodes;

// Improved memory management
void register_node(ASTNode* node) {
    if (node) all_nodes.push_back(node);
}

// Function to clean up AST nodes (declared here, defined after main)
void cleanup_nodes();

// Replace the get_return_var function with a simpler version
std::string get_return_var(const std::string& func_name) {
    return func_name + "_result";
}

// Get Promela type for C type
std::string get_promela_type(const std::string& c_type) {
    if (c_type == "int") return "int";
    if (c_type == "float" || c_type == "double") return "int"; // Use int for float/double
    if (c_type == "char") return "byte"; // Use byte for char
    return "int"; // Default to int
}

%}

/* Parser configuration */
%define parse.error verbose
%define parse.lac full

/* Yylval union - must match what's used in lexer */
%union {
    int num;
    double dval;
    char* id;
    char* str;
    char chr;
    char op;
    
    // AST node types
    ASTNode* node;
    ProgramNode* program;
    VarDeclNode* var_decl;
    FunctionNode* func_decl;
    CompoundStmtNode* compound_stmt;
    IfStmtNode* if_stmt;
    WhileStmtNode* while_stmt;
    PrintfStmtNode* printf_stmt;
    ReturnStmtNode* return_stmt;
    ExprStmtNode* expr_stmt;
    
    // Container types
    std::vector<ASTNode*>* node_list;
    std::pair<std::string, std::string>* param;
    std::vector<std::pair<std::string, std::string>>* param_list;
}

/* Token definitions */
%token INT FLOAT DOUBLE CHAR IF ELSE WHILE RETURN PRINTF
%token CHAN OF  /* Add these two tokens */
%token <num> NUMBER
%token <dval> FLOAT_VAL
%token <id> IDENTIFIER
%token <str> STRING_LITERAL
%token <chr> CHAR_VAL
%token EQ NE LE GE AND OR

/* Operator precedence - lowest to highest */
%left OR
%left AND
%left EQ NE
%left '<' '>' LE GE
%left '+' '-'
%left '*' '/' '%'
%right UMINUS '!'

/* Fix for dangling else problem */
%nonassoc IF_WITHOUT_ELSE
%nonassoc ELSE

/* Types for non-terminals */
%type <program> program
%type <node_list> declaration_list statement_list argument_list
%type <node> declaration statement expression assignment_expression logical_or_expression
%type <node> logical_and_expression equality_expression relational_expression
%type <node> additive_expression multiplicative_expression unary_expression
%type <node> postfix_expression primary_expression
%type <var_decl> variable_declaration
%type <func_decl> function_definition
%type <param> parameter
%type <param_list> parameter_list
%type <compound_stmt> compound_statement
%type <if_stmt> selection_statement
%type <while_stmt> iteration_statement
%type <printf_stmt> printf_statement
%type <return_stmt> return_statement
%type <expr_stmt> expression_statement

/* Starting symbol */
%start program

%%

program
    : declaration_list
        {
            auto prog = new ProgramNode();
            prog->declarations = *$1;
            $$ = prog;
            root = prog;
            register_node(prog);
            delete $1;
        }
    ;

declaration_list
    : declaration
        {
            $$ = new std::vector<ASTNode*>();
            if ($1) $$->push_back($1);
        }
    | declaration_list declaration
        {
            $$ = $1;
            if ($2) $$->push_back($2);
        }
    ;

declaration
    : variable_declaration
        {
            $$ = $1;
        }
    | function_definition
        {
            $$ = $1;
        }
    ;

// Add array declaration rule to your variable_declaration section
variable_declaration
    : INT IDENTIFIER ';'
        {
            $$ = new VarDeclNode("int", $2);
            register_node($$);
            free($2);
        }
    | INT IDENTIFIER '[' NUMBER ']' ';'
        {
            // Create array declaration
            $$ = new VarDeclNode("int", $2, $4);
            $$->arraySize = $4;  // Set array size
            register_node($$);
            free($2);
        }
    | FLOAT IDENTIFIER ';'
        {
            $$ = new VarDeclNode("float", $2);
            register_node($$);
            free($2);
        }
    | FLOAT IDENTIFIER '=' expression ';'
        {
            $$ = new VarDeclNode("float", $2, $4);
            register_node($$);
            free($2);
        }
    | FLOAT IDENTIFIER '[' NUMBER ']' ';'
        {
            $$ = new ArrayDeclNode("float", $2, $4);
            register_node($$);
            free($2);
        }
    | DOUBLE IDENTIFIER ';'
        {
            $$ = new VarDeclNode("double", $2);
            register_node($$);
            free($2);
        }
    | DOUBLE IDENTIFIER '=' expression ';'
        {
            $$ = new VarDeclNode("double", $2, $4);
            register_node($$);
            free($2);
        }
    | DOUBLE IDENTIFIER '[' NUMBER ']' ';'
        {
            $$ = new ArrayDeclNode("double", $2, $4);
            register_node($$);
            free($2);
        }
    | CHAR IDENTIFIER ';'
        {
            $$ = new VarDeclNode("char", $2);
            register_node($$);
            free($2);
        }
    | CHAR IDENTIFIER '=' expression ';'
        {
            $$ = new VarDeclNode("char", $2, $4);
            register_node($$);
            free($2);
        }
    | CHAR IDENTIFIER '[' NUMBER ']' ';'
        {
            $$ = new ArrayDeclNode("char", $2, $4);
            register_node($$);
            free($2);
        }
    ;

function_definition
    : INT IDENTIFIER '(' parameter_list ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("int", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("int", $2, $7);
            if ($4) {
                $$->parameters = *$4;
                delete $4;
            }
            register_node($$);
            free($2);
        }
    | FLOAT IDENTIFIER '(' parameter_list ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("float", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("float", $2, $7);
            if ($4) {
                $$->parameters = *$4;
                delete $4;
            }
            register_node($$);
            free($2);
        }
    | DOUBLE IDENTIFIER '(' parameter_list ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("double", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("double", $2, $7);
            if ($4) {
                $$->parameters = *$4;
                delete $4;
            }
            register_node($$);
            free($2);
        }
    | CHAR IDENTIFIER '(' parameter_list ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("char", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("char", $2, $7);
            if ($4) {
                $$->parameters = *$4;
                delete $4;
            }
            register_node($$);
            free($2);
        }
    | INT IDENTIFIER '(' ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("int", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("int", $2, $6);
            register_node($$);
            free($2);
        }
    | FLOAT IDENTIFIER '(' ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("float", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("float", $2, $6);
            register_node($$);
            free($2);
        }
    | DOUBLE IDENTIFIER '(' ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("double", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("double", $2, $6);
            register_node($$);
            free($2);
        }
    | CHAR IDENTIFIER '(' ')'
        {
            current_function_name = $2;
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("char", $2));
        }
      compound_statement
        {
            $$ = new FunctionNode("char", $2, $6);
            register_node($$);
            free($2);
        }
    ;

// Fix the parameter_list rule
parameter_list
    : parameter
        {
            $$ = new std::vector<std::pair<std::string, std::string>>();
            $$->push_back(*$1);
            delete $1;
        }
    | parameter_list ',' parameter
        {
            $$ = $1;
            $$->push_back(*$3);
            delete $3;
        }
    ;

parameter
    : INT IDENTIFIER
        {
            $$ = new std::pair<std::string, std::string>("int", $2);
            free($2);
        }
    | FLOAT IDENTIFIER
        {
            $$ = new std::pair<std::string, std::string>("float", $2);
            free($2);
        }
    | DOUBLE IDENTIFIER
        {
            $$ = new std::pair<std::string, std::string>("double", $2);
            free($2);
        }
    | CHAR IDENTIFIER
        {
            $$ = new std::pair<std::string, std::string>("char", $2);
            free($2);
        }
    ;

compound_statement
    : '{' 
        {
            // Use explicit type for mid-rule action
            $<compound_stmt>$ = new CompoundStmtNode();
            register_node($<compound_stmt>$);
        }
      statement_list '}'
        {
            // Reference the mid-rule action with proper type
            $$ = $<compound_stmt>2;
            if ($3) {
                $$->statements = *$3;
                delete $3;
            }
        }
    | '{' '}'
        {
            $$ = new CompoundStmtNode();
            register_node($$);
        }
    ;

statement_list
    : statement
        {
            $$ = new std::vector<ASTNode*>();
            if ($1) $$->push_back($1);
        }
    | statement_list statement
        {
            $$ = $1;
            if ($2) $$->push_back($2);
        }
    ;

statement
    : expression_statement
        {
            $$ = $1;
        }
    | compound_statement
        {
            $$ = $1;
        }
    | selection_statement
        {
            $$ = $1;
        }
    | iteration_statement
        {
            $$ = $1;
        }
    | printf_statement
        {
            $$ = $1;
        }
    | return_statement
        {
            $$ = $1;
        }
    | variable_declaration
        {
            $$ = $1;
        }
    ;

expression_statement
    : ';'
        {
            $$ = new ExprStmtNode(nullptr);  // Empty statement
            register_node($$);
        }
    | expression ';'
        {
            $$ = new ExprStmtNode($1);
            register_node($$);
        }
    ;

selection_statement
    : IF '(' expression ')' statement %prec IF_WITHOUT_ELSE
        {
            // Simple version - no buffer needed
            $$ = new IfStmtNode($3, $5);
            register_node($$);
        }
    | IF '(' expression ')' statement ELSE statement
        {
            // Simple version - no buffer needed
            $$ = new IfStmtNode($3, $5, $7);
            register_node($$);
        }
    ;

iteration_statement
    : WHILE '(' expression ')' statement
        {
            $$ = new WhileStmtNode($3, $5);
            register_node($$);
        }
    ;


printf_statement
    : PRINTF '(' STRING_LITERAL ')' ';'
        {
            $$ = new PrintfStmtNode($3);
            register_node($$);
            free($3);
        }
    | PRINTF '(' STRING_LITERAL ',' argument_list ')' ';'
        {
            $$ = new PrintfStmtNode($3);
            $$->args = *$5;
            register_node($$);
            free($3);
            delete $5;
        }
    ;

return_statement
    : RETURN expression ';'
        {
            $$ = new ReturnStmtNode($2, current_function_name);
            register_node($$);
        }
    | RETURN ';'
        {
            $$ = new ReturnStmtNode(nullptr, current_function_name);
            register_node($$);
        }
    ;

argument_list
    : expression
        {
            $$ = new std::vector<ASTNode*>();
            $$->push_back($1);
        }
    | argument_list ',' expression
        {
            $$ = $1;
            $$->push_back($3);
        }
    ;

expression
    : assignment_expression
        {
            $$ = $1;
        }
    ;

assignment_expression
    : logical_or_expression
        {
            $$ = $1;
        }
    | postfix_expression '=' assignment_expression
        {
            // Special case: if right side is a function call, we need to split this
            if (auto* funcCall = dynamic_cast<FunctionCallNode*>($3)) {
                // Create a compound statement representing run + use of global var
                auto compound = new CompoundStmtNode();
                
                // Create the run statement
                auto runExpr = new ExprStmtNode($3);
                compound->statements.push_back(runExpr);
                
                // Get the appropriate global variable name
                std::string returnVar = funcCall->name + "_result";
                
                // Create assignment from global var to target variable
                auto global = new IdentifierNode(returnVar);
                auto assign = new BinaryExprNode($1, BinaryExprNode::ASSIGN, global);
                auto assignStmt = new ExprStmtNode(assign);
                
                compound->statements.push_back(assignStmt);
                
                $$ = compound;
            } else {
                // Normal assignment
                $$ = new BinaryExprNode($1, BinaryExprNode::ASSIGN, $3);
            }
            
            register_node($$);
        }
    ;

logical_or_expression
    : logical_and_expression
        {
            $$ = $1;
        }
    | logical_or_expression OR logical_and_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::OR, $3);
            register_node($$);
        }
    ;

logical_and_expression
    : equality_expression
        {
            $$ = $1;
        }
    | logical_and_expression AND equality_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::AND, $3);
            register_node($$);
        }
    ;

equality_expression
    : relational_expression
        {
            $$ = $1;
        }
    | equality_expression EQ relational_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::EQ, $3);
            register_node($$);
        }
    | equality_expression NE relational_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::NE, $3);
            register_node($$);
        }
    ;

relational_expression
    : additive_expression
        {
            $$ = $1;
        }
    | relational_expression '<' additive_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::LT, $3);
            register_node($$);
        }
    | relational_expression '>' additive_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::GT, $3);
            register_node($$);
        }
    | relational_expression LE additive_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::LE, $3);
            register_node($$);
        }
    | relational_expression GE additive_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::GE, $3);
            register_node($$);
        }
    ;

additive_expression
    : multiplicative_expression
        {
            $$ = $1;
        }
    | additive_expression '+' multiplicative_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::ADD, $3);
            register_node($$);
        }
    | additive_expression '-' multiplicative_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::SUB, $3);
            register_node($$);
        }
    ;

multiplicative_expression
    : unary_expression
        {
            $$ = $1;
        }
    | multiplicative_expression '*' unary_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::MUL, $3);
            register_node($$);
        }
    | multiplicative_expression '/' unary_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::DIV, $3);
            register_node($$);
        }
    | multiplicative_expression '%' unary_expression
        {
            $$ = new BinaryExprNode($1, BinaryExprNode::MOD, $3);
            register_node($$);
        }
    ;

unary_expression
    : postfix_expression
        {
            $$ = $1;
        }
    | '-' unary_expression %prec UMINUS
        {
            $$ = new UnaryExprNode(UnaryExprNode::MINUS, $2);
            register_node($$);
        }
    | '!' unary_expression
        {
            $$ = new UnaryExprNode(UnaryExprNode::NOT, $2);
            register_node($$);
        }
    ;

// Fix postfix_expression rule to handle array access
postfix_expression
    : primary_expression
        {
            $$ = $1;  // Pass through
        }
    | postfix_expression '[' expression ']'
        {
            // Create array access node from expression
            $$ = new ArrayAccessNode($1, $3);
            register_node($$);
        }
    | IDENTIFIER '(' ')'
        {
            $$ = new FunctionCallNode($1);
            register_node($$);
            free($1);
        }
    | IDENTIFIER '(' argument_list ')'
        {
            auto call = new FunctionCallNode($1);
            call->args = *$3;
            $$ = call;
            register_node($$);
            free($1);
            delete $3;
        }
    ;

// Make sure primary_expression only handles basic expressions
primary_expression
    : IDENTIFIER
        {
            $$ = new IdentifierNode($1);
            register_node($$);
            free($1);
        }
    | NUMBER
        {
            $$ = new NumberNode($1);
            register_node($$);
        }
    | FLOAT_VAL
        {
            $$ = new FloatNode($1);
            register_node($$);
        }
    | CHAR_VAL
        {
            $$ = new CharNode($1);
            register_node($$);
        }
    | '(' expression ')'
        {
            $$ = $2;
        }
    ;

%%

void yyerror(const char* s) {
    fprintf(stderr, "Error at line %d: %s near '%s'\n", yylineno, s, yytext);
}

// Function to clean up AST nodes
void cleanup_nodes() {
    for (auto node : all_nodes) {
        delete node;
    }
    all_nodes.clear();
}

// Add to the parser.y main() function to ensure global return variables are declared:

int main(int argc, char** argv) {
    // If input file provided, use it
    extern FILE* yyin;
    if (argc > 1) {
        FILE* input = fopen(argv[1], "r");
        if (!input) {
            fprintf(stderr, "Error: Could not open input file %s\n", argv[1]);
            return 1;
        }
        yyin = input;
    }
    
    // Parse input and build AST
    yyparse();
    
    // Print header for Promela code
    std::cout << "/* Generated Promela code */\n";
    std::cout << "/* Translated from C using C-to-Promela translator */\n";
    std::cout << "/* Warning: Some C semantics may not be preserved */\n\n";
    
    // Generate regular globals first
    if (root) {
        // First pass to output global variables
        for (auto decl : root->declarations) {
            if (auto var_decl = dynamic_cast<VarDeclNode*>(decl)) {
                var_decl->generate_code();
            }
        }
    }
    
    // Generate global return value variables
    std::cout << "\n/* Globals to simulate return values */\n";

    // Generate return variables for each function defined in the source
    for (const auto& func : function_returns) {
        std::string type = func.first;
        std::string name = func.second;
        std::string promela_type = get_promela_type(type);
        std::cout << promela_type << " " << name << "_result;\n";
    }
    std::cout << "\n";
    
    // Generate function definitions
    if (root) {
        // Second pass to output function definitions
        for (auto decl : root->declarations) {
            if (dynamic_cast<VarDeclNode*>(decl) == nullptr) {
                decl->generate_code();
            }
        }
    }
    
    // Clean up
    cleanup_nodes();
    
    return 0;
}