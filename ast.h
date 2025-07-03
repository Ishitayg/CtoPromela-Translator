#ifndef AST_H
#define AST_H

#include <iostream>
#include <string>
#include <vector>
#include <memory>
#include <utility>  // Required for std::pair

// Update the forward declarations at the top of the file:

// Forward declarations
class FunctionCallNode;
class BreakStmtNode;
class CaseNode;
class BinaryExprNode;  // Add this line

// For indentation
extern int indent_level;
std::string get_indent();

// Forward declaration
std::string get_promela_type(const std::string& c_type);

// Base AST Node class
class ASTNode {
public:
    virtual ~ASTNode() = default;
    virtual void generate_code() const = 0;
};

// Program node - root of the AST
class ProgramNode : public ASTNode {
public:
    std::vector<ASTNode*> declarations;
    
    ~ProgramNode() override = default;
    
    void generate_code() const override {
        for (auto decl : declarations) {
            decl->generate_code();
        }
    }
};

// Variable declaration node
class VarDeclNode : public ASTNode {
public:
    std::string type;
    std::string name;
    ASTNode* initializer = nullptr;
    FunctionCallNode* functionCall = nullptr;
    int arraySize = -1;  // -1 means not an array, >=0 is array size

    // Regular variable
    VarDeclNode(const std::string& t, const std::string& n)
        : type(t), name(n) {}
    
    // Array variable
    VarDeclNode(const std::string& t, const std::string& n, int size)
        : type(t), name(n), arraySize(size) {}
    
    // With initializer
    VarDeclNode(const std::string& t, const std::string& n, ASTNode* init)
        : type(t), name(n), initializer(init) {}
    
    ~VarDeclNode() override = default;
    
    // Just declare the method here, don't define it
    void generate_code() const override;
};

// Function declaration node
class FunctionNode : public ASTNode {
public:
    std::string returnType;
    std::string name;
    std::vector<std::pair<std::string, std::string>> parameters; // (type, name)
    ASTNode* body;
    
    FunctionNode(const std::string& rt, const std::string& n, ASTNode* b)
        : returnType(rt), name(n), body(b) {}
    
    ~FunctionNode() override = default;
    
    void generate_code() const override {
        if (name == "main") {
            // Regular proctype in the new implementation (not active)
            std::cout << "proctype " << name << "(";
        } else {
            std::cout << "proctype " << name << "(";
        }
        
        // Generate parameter list
        for (size_t i = 0; i < parameters.size(); i++) {
            if (i > 0) std::cout << ", ";
            
            // Map C types to Promela types
            if (parameters[i].first == "int") {
                std::cout << "int " << parameters[i].second;
            } else if (parameters[i].first == "float" || parameters[i].first == "double") {
                std::cout << "int " << parameters[i].second << " /* " << parameters[i].first << " */";
            } else if (parameters[i].first == "char") {
                std::cout << "byte " << parameters[i].second;
            } else {
                std::cout << "int " << parameters[i].second << " /* unknown type " << parameters[i].first << " */";
            }
        }
        std::cout << ")" << std::endl;
        
        // Generate function body
        body->generate_code();
    }
};

// Array Access Node (already exists but reviewed for correctness)
class ArrayAccessNode : public ASTNode {
public:
    ASTNode* array;  // Changed from string to ASTNode*
    ASTNode* index;
    
    // Updated constructor that takes two AST nodes
    ArrayAccessNode(ASTNode* arr, ASTNode* idx)
        : array(arr), index(idx) {}
    
    ~ArrayAccessNode() override = default;
    
    void generate_code() const override {
        // Generate array expression (could be identifier or another array access)
        array->generate_code();
        std::cout << "[";
        index->generate_code();
        std::cout << "]";
    }
};

// Channel Declaration Node
class ChannelDeclNode : public ASTNode {
public:
    std::string name;
    int capacity;
    std::vector<std::string> messageTypes;
    
    ChannelDeclNode(const std::string& n, int cap, const std::vector<std::string>& types)
        : name(n), capacity(cap), messageTypes(types) {}
    
    ~ChannelDeclNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << "chan " << name << " = [" << capacity << "] of {";
        
        for (size_t i = 0; i < messageTypes.size(); i++) {
            if (i > 0) std::cout << ", ";
            std::cout << get_promela_type(messageTypes[i]);
        }
        
        std::cout << "};" << std::endl;
    }
};

// Channel Send Operation Node
class ChannelSendNode : public ASTNode {
public:
    std::string channelName;
    std::vector<ASTNode*> messageValues;
    
    ChannelSendNode(const std::string& ch, const std::vector<ASTNode*>& values)
        : channelName(ch), messageValues(values) {}
    
    ~ChannelSendNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << channelName << "!";
        
        for (size_t i = 0; i < messageValues.size(); i++) {
            if (i > 0) std::cout << ",";
            messageValues[i]->generate_code();
        }
        
        std::cout << ";" << std::endl;
    }
};

// Channel Receive Operation Node
class ChannelRecvNode : public ASTNode {
public:
    std::string channelName;
    std::vector<std::string> variables;
    
    ChannelRecvNode(const std::string& ch, const std::vector<std::string>& vars)
        : channelName(ch), variables(vars) {}
    
    ~ChannelRecvNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << channelName << "?";
        
        for (size_t i = 0; i < variables.size(); i++) {
            if (i > 0) std::cout << ",";
            std::cout << variables[i];
        }
        
        std::cout << ";" << std::endl;
    }
};

// Compound statement node
class CompoundStmtNode : public ASTNode {
public:
    std::vector<ASTNode*> statements;
    
    ~CompoundStmtNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << "{" << std::endl;
        indent_level++;
        
        for (auto stmt : statements) {
            stmt->generate_code();
        }
        
        indent_level--;
        std::cout << get_indent() << "}" << std::endl;
    }
};

// Expression statement node
class ExprStmtNode : public ASTNode {
public:
    ASTNode* expression; // May be nullptr for empty statements
    
    explicit ExprStmtNode(ASTNode* expr = nullptr) : expression(expr) {}
    
    ~ExprStmtNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent();
        if (expression) {
            expression->generate_code();
        } else {
            std::cout << "skip";
        }
        std::cout << ";" << std::endl;
    }
};

// If statement node
class IfStmtNode : public ASTNode {
public:
    ASTNode* condition;
    ASTNode* thenBranch;
    ASTNode* elseBranch; // May be nullptr
    
    IfStmtNode(ASTNode* cond, ASTNode* then, ASTNode* else_branch = nullptr)
        : condition(cond), thenBranch(then), elseBranch(else_branch) {}
    
    ~IfStmtNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << "if" << std::endl;
        
        std::cout << get_indent() << ":: (";
        condition->generate_code();
        std::cout << ") -> " << std::endl;
        
        indent_level++;
        thenBranch->generate_code();
        indent_level--;
        
        std::cout << get_indent() << ":: else -> ";
        if (elseBranch) {
            std::cout << std::endl;
            indent_level++;
            elseBranch->generate_code();
            indent_level--;
        } else {
            std::cout << "skip" << std::endl;
        }
        
        std::cout << get_indent() << "fi;" << std::endl;
    }
};

// While statement node
class WhileStmtNode : public ASTNode {
public:
    ASTNode* condition;
    ASTNode* body;
    
    WhileStmtNode(ASTNode* cond, ASTNode* b) : condition(cond), body(b) {}
    
    ~WhileStmtNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << "do" << std::endl;
        
        std::cout << get_indent() << ":: (";
        condition->generate_code();
        std::cout << ") -> " << std::endl;
        
        indent_level++;
        body->generate_code();
        indent_level--;
        
        std::cout << get_indent() << ":: else -> break" << std::endl;
        std::cout << get_indent() << "od;" << std::endl;
    }
};

// Return statement node
class ReturnStmtNode : public ASTNode {
public:
    ASTNode* value; // May be nullptr
    std::string functionName;
    
    ReturnStmtNode(ASTNode* val, const std::string& func)
        : value(val), functionName(func) {}
    
    ~ReturnStmtNode() override = default;
    
    void generate_code() const override {
        // Get appropriate global variable for this function's return value
        std::string returnVar = functionName + "_result";
        
        if (value) {
            // Assign the return value to the appropriate global variable
            std::cout << get_indent() << returnVar << " = ";
            value->generate_code();
            std::cout << ";" << std::endl;
        }
        
        // Keep the comment for clarity
        std::cout << get_indent() << "// return ";
        if (value) {
            value->generate_code();
        }
        std::cout << " (Promela doesn't support return values)" << std::endl;
    }
};

// Printf statement node
class PrintfStmtNode : public ASTNode {
public:
    std::string format;
    std::vector<ASTNode*> args;
    
    explicit PrintfStmtNode(const std::string& fmt) : format(fmt) {}
    
    ~PrintfStmtNode() override = default;
    
    void generate_code() const override {
        std::cout << get_indent() << "// Note: printf in Promela only executes during simulation, not verification" << std::endl;
        
        // Make a local copy of the format string
        std::string fixed_format = format;
        
        // Replace all %f with %d since Promela uses int for floats
        size_t pos = 0;
        while ((pos = fixed_format.find("%f", pos)) != std::string::npos) {
            fixed_format.replace(pos, 2, "%d");
            pos += 2;
        }
        
        std::cout << get_indent() << "printf(" << fixed_format;
        
        if (!args.empty()) {
            std::cout << ", ";
            for (size_t i = 0; i < args.size(); i++) {
                if (i > 0) std::cout << ", ";
                args[i]->generate_code();
            }
        }
        
        std::cout << ");" << std::endl;
    }
};

// Unary expression node
class UnaryExprNode : public ASTNode {
public:
    enum Op { MINUS, NOT };
    
    Op op;
    ASTNode* operand;
    
    UnaryExprNode(Op o, ASTNode* e) : op(o), operand(e) {}
    
    ~UnaryExprNode() override = default;
    
    // Just declare the function here
    void generate_code() const override;
};

// Binary expression node
class BinaryExprNode : public ASTNode {
public:
    enum Op { ADD, SUB, MUL, DIV, MOD, EQ, NE, LT, GT, LE, GE, AND, OR, ASSIGN };
    
    ASTNode* left;
    ASTNode* right;
    Op op;
    
    BinaryExprNode(ASTNode* l, Op o, ASTNode* r) : left(l), right(r), op(o) {}
    
    ~BinaryExprNode() override = default;
    
    void generate_code() const override {
        left->generate_code();
        
        switch (op) {
            case ADD: std::cout << " + "; break;
            case SUB: std::cout << " - "; break;
            case MUL: std::cout << " * "; break;
            case DIV: std::cout << " / "; break;
            case MOD: std::cout << " % "; break;
            case EQ: std::cout << " == "; break;
            case NE: std::cout << " != "; break;
            case LT: std::cout << " < "; break;
            case GT: std::cout << " > "; break;
            case LE: std::cout << " <= "; break;
            case GE: std::cout << " >= "; break;
            case AND: std::cout << " && "; break;
            case OR: std::cout << " || "; break;
            case ASSIGN: std::cout << " = "; break;
        }
        
        right->generate_code();
    }
};

// Identifier node
class IdentifierNode : public ASTNode {
public:
    std::string name;
    
    explicit IdentifierNode(const std::string& n) : name(n) {}
    
    ~IdentifierNode() override = default;
    
    void generate_code() const override {
        std::cout << name;
    }
};

// Number node
class NumberNode : public ASTNode {
public:
    int value;
    
    explicit NumberNode(int val) : value(val) {}
    
    ~NumberNode() override = default;
    
    void generate_code() const override {
        std::cout << value;
    }
};

// Float node
class FloatNode : public ASTNode {
public:
    double value;
    
    explicit FloatNode(double val) : value(val) {}
    
    ~FloatNode() override = default;
    
    void generate_code() const override {
        // Convert to integer approximation for Promela
        std::cout << static_cast<int>(value);
    }
};

// Char node
class CharNode : public ASTNode {
public:
    char value;
    
    explicit CharNode(char val) : value(val) {}
    
    ~CharNode() override = default;
    
    void generate_code() const override {
        std::cout << static_cast<int>(value) << " /* '" << value << "' */";
    }
};

// Function call node
class FunctionCallNode : public ASTNode {
public:
    std::string name;
    std::vector<ASTNode*> args;
    
    // Constructor with arguments
    FunctionCallNode(const std::string& n, const std::vector<ASTNode*>& arguments)
        : name(n), args(arguments) {}
    
    // Constructor for empty arguments - needed for IDENTIFIER '(' ')'
    FunctionCallNode(const std::string& n, std::initializer_list<ASTNode*> arguments = {})
        : name(n), args(arguments) {}
    
    ~FunctionCallNode() override = default;
    
    void generate_code() const override {
        // Same implementation as before
        std::cout << "run " << name << "(";
        
        // Handle arguments
        for (size_t i = 0; i < args.size(); i++) {
            if (i > 0) std::cout << ", ";
            args[i]->generate_code();
        }
        
        std::cout << ")";
    }
};

// For Loop Node
class ForStmtNode : public ASTNode {
public:
    ASTNode* init;      // Initialization expression (may be nullptr)
    ASTNode* condition; // Loop condition (may be nullptr)
    ASTNode* increment; // Increment expression (may be nullptr)
    ASTNode* body;      // Loop body
    
    ForStmtNode(ASTNode* i, ASTNode* c, ASTNode* inc, ASTNode* b)
        : init(i), condition(c), increment(inc), body(b) {}
    
    ~ForStmtNode() override = default;
    
    void generate_code() const override {
        // Generate initialization if it exists
        if (init) {
            std::cout << get_indent();
            init->generate_code();
            std::cout << ";" << std::endl;
        }
        
        // Create Promela do loop
        std::cout << get_indent() << "do" << std::endl;
        
        // Generate condition (default to true if no condition)
        std::cout << get_indent() << ":: (";
        if (condition) 
            condition->generate_code();
        else 
            std::cout << "true";
        std::cout << ") -> " << std::endl;
        
        // Generate loop body
        indent_level++;
        std::cout << get_indent() << "{" << std::endl;
        indent_level++;
        
        // Generate the body
        body->generate_code();
        
        // Add increment at the end if it exists
        if (increment) {
            std::cout << get_indent();
            increment->generate_code();
            std::cout << ";" << std::endl;
        }
        
        indent_level--;
        std::cout << get_indent() << "}" << std::endl;
        indent_level--;
        
        // Add the break condition
        std::cout << get_indent() << ":: else -> break" << std::endl;
        std::cout << get_indent() << "od;" << std::endl;
    }
};

// Do-While Loop Node
class DoWhileStmtNode : public ASTNode {
public:
    ASTNode* body;
    ASTNode* condition;
    
    DoWhileStmtNode(ASTNode* b, ASTNode* c) : body(b), condition(c) {}
    
    ~DoWhileStmtNode() override = default;
    
    void generate_code() const override {
        // In Promela, we use a do loop with a condition check at the end
        std::cout << get_indent() << "do" << std::endl;
        std::cout << get_indent() << ":: true -> " << std::endl;
        
        // Generate body
        indent_level++;
        std::cout << get_indent() << "{" << std::endl;
        indent_level++;
        body->generate_code();
        
        // Add condition check at the end of each iteration
        std::cout << get_indent() << "if" << std::endl;
        std::cout << get_indent() << ":: !(";
        condition->generate_code();
        std::cout << ") -> break" << std::endl;
        std::cout << get_indent() << ":: else -> skip" << std::endl;
        std::cout << get_indent() << "fi;" << std::endl;
        
        indent_level--;
        std::cout << get_indent() << "}" << std::endl;
        indent_level--;
        
        std::cout << get_indent() << ":: else -> skip" << std::endl;
        std::cout << get_indent() << "od;" << std::endl;
    }
};

// Break Statement Node
class BreakStmtNode : public ASTNode {
public:
    BreakStmtNode() {}
    
    ~BreakStmtNode() override = default;
    
    void generate_code() const override {
        // The actual code will be generated by the parent switch/loop statement
        // This placeholder ensures breaks are recognized in the source
        std::cout << get_indent() << "// Break statement" << std::endl;
    }
};

// Case Node for Switch statements
class CaseNode : public ASTNode {
public:
    ASTNode* value;  // nullptr for default case
    std::vector<ASTNode*> statements;
    bool has_break;
    
    CaseNode(ASTNode* val, const std::vector<ASTNode*>& stmts)
        : value(val), statements(stmts) {
        // Check if this case has a break statement
        has_break = false;
        for (auto stmt : statements) {
            if (dynamic_cast<BreakStmtNode*>(stmt)) {
                has_break = true;
                break;
            }
        }
    }
    
    ~CaseNode() override = default;
    
    void generate_code() const override {
        // This will be handled by SwitchStmtNode
        std::cout << "// Case node should be generated by parent switch" << std::endl;
    }
};

// Switch Statement Node
class SwitchStmtNode : public ASTNode {
public:
    ASTNode* expression;
    std::vector<CaseNode*> cases;
    
    SwitchStmtNode(ASTNode* expr, const std::vector<CaseNode*>& c)
        : expression(expr), cases(c) {}
    
    ~SwitchStmtNode() override = default;
    
    void generate_code() const override {
        // In Promela, switch statements are implemented using if-goto structure
        std::cout << get_indent() << "// Switch statement translated to Promela if-goto" << std::endl;
        
        // Step 1: Evaluate the expression once and store it
        std::cout << get_indent() << "int _switch_expr = ";
        expression->generate_code();
        std::cout << ";" << std::endl;
        
        // Step 2: Create a dispatcher to jump to the right case
        for (size_t i = 0; i < cases.size(); i++) {
            if (!cases[i]->value) continue; // Skip default case in initial check
            
            std::cout << get_indent() << "if" << std::endl;
            std::cout << get_indent() << ":: (_switch_expr == ";
            cases[i]->value->generate_code();
            std::cout << ") -> goto _case_" << i << ";" << std::endl;
            std::cout << get_indent() << ":: else -> skip;" << std::endl;
            std::cout << get_indent() << "fi;" << std::endl;
        }
        
        // Handle default case or no matches
        bool has_default = false;
        size_t default_idx = 0;
        
        for (size_t i = 0; i < cases.size(); i++) {
            if (!cases[i]->value) {
                has_default = true;
                default_idx = i;
                break;
            }
        }
        
        if (has_default) {
            std::cout << get_indent() << "// No matching case, go to default" << std::endl;
            std::cout << get_indent() << "goto _case_" << default_idx << ";" << std::endl;
        } else {
            std::cout << get_indent() << "// No matching case, and no default" << std::endl;
            std::cout << "goto _end_switch;" << std::endl;
        }
        
        // Generate actual case code
        for (size_t i = 0; i < cases.size(); i++) {
            // Label for this case
            std::cout << get_indent() << "_case_" << i << ": // ";
            if (cases[i]->value) {
                std::cout << "case ";
                cases[i]->value->generate_code();
                std::cout << std::endl;
            } else {
                std::cout << "default" << std::endl;
            }
            
            // Generate statements for this case
            indent_level++;
            for (auto& stmt : cases[i]->statements) {
                if (dynamic_cast<BreakStmtNode*>(stmt)) {
                    std::cout << get_indent() << "goto _end_switch; // break" << std::endl;
                } else {
                    stmt->generate_code();
                }
            }
            
            // If this case doesn't have a break and isn't the last case,
            // add explicit fall-through to next case
            if (!cases[i]->has_break && i < cases.size() - 1) {
                std::cout << get_indent() << "// Fall-through to next case" << std::endl;
                std::cout << get_indent() << "goto _case_" << (i + 1) << ";" << std::endl;
            } else if (!cases[i]->has_break) {
                // Last case without a break still needs to go to the end
                std::cout << get_indent() << "goto _end_switch;  // implicit end of switch" << std::endl;
            }
            indent_level--;
        }
        
        // End label for the switch
        std::cout << get_indent() << "_end_switch: skip; // end of switch statement" << std::endl;
    }
};

// Implementation of VarDeclNode::generate_code
inline void VarDeclNode::generate_code() const {
    // Map C types to Promela types
    std::string promela_type;
    if (type == "int") {
        promela_type = "int";
    } else if (type == "float" || type == "double") {
        promela_type = "int"; // Promela uses integers for approximating floats
        std::cout << get_indent() << "// Note: " << type << " is approximated using int in Promela" << std::endl;
    } else if (type == "char") {
        promela_type = "byte"; // Promela uses byte for char
    } else {
        promela_type = "int"; // Default fallback
        std::cout << get_indent() << "// Warning: Unsupported type '" << type << "' defaulting to int" << std::endl;
    }
    
    if (arraySize >= 0) {
        // This is an array declaration
        std::cout << get_indent() << promela_type << " " << name << "[" << arraySize << "]";
        
        if (initializer) {
            std::cout << " = ";
            initializer->generate_code();
        }
        std::cout << ";" << std::endl;
    }
    // Special handling for variables initialized with function calls
    else if (functionCall) {
        // First declare the variable
        std::cout << get_indent() << promela_type << " " << name << ";" << std::endl;
        
        // Then generate the function call (run statement)
        std::cout << get_indent();
        functionCall->generate_code();
        std::cout << ";" << std::endl;
        
        // Then assign from the global return variable
        // Fix: construct return variable name from function name
        std::string returnVarName = functionCall->name + "_result";
        std::cout << get_indent() << name << " = " << returnVarName << ";" << std::endl;
    }
    else if (initializer) {
        std::cout << get_indent() << promela_type << " " << name << " = ";
        initializer->generate_code();
        std::cout << ";" << std::endl;
    } else {
        std::cout << get_indent() << promela_type << " " << name << ";" << std::endl;
    }
}

// Move the implementation to the end of the file, after BinaryExprNode is defined
// Add this just before the #endif line, after VarDeclNode::generate_code implementation
inline void UnaryExprNode::generate_code() const {
    switch (op) {
        case MINUS:
            std::cout << "-";
            break;
        case NOT:
            std::cout << "!";
            break;
    }
    
    // For complex expressions, use parentheses
    bool needsParens = dynamic_cast<BinaryExprNode*>(operand) != nullptr;
    if (needsParens) std::cout << "(";
    
    operand->generate_code();
    
    if (needsParens) std::cout << ")";
}

// Add these classes at the end before the #endif line

// Postfix increment node
class PostIncrementNode : public ASTNode {
public:
    ASTNode* expression;
    
    explicit PostIncrementNode(ASTNode* expr) : expression(expr) {}
    
    ~PostIncrementNode() override = default;
    
    void generate_code() const override {
        // For expressions like i++, we generate i = i + 1
        auto* id = dynamic_cast<IdentifierNode*>(expression);
        if (id) {
            std::cout << id->name << " = " << id->name << " + 1";
        } else {
            // For complex expressions, do the best we can
            expression->generate_code();
            std::cout << " + 1";
        }
    }
};

// Postfix decrement node
class PostDecrementNode : public ASTNode {
public:
    ASTNode* expression;
    
    explicit PostDecrementNode(ASTNode* expr) : expression(expr) {}
    
    ~PostDecrementNode() override = default;
    
    void generate_code() const override {
        // For expressions like i--, we generate i = i - 1
        auto* id = dynamic_cast<IdentifierNode*>(expression);
        if (id) {
            std::cout << id->name << " = " << id->name << " - 1";
        } else {
            // For complex expressions, do the best we can
            expression->generate_code();
            std::cout << " - 1";
        }
    }
};

// Add this class if it doesn't exist
class ArrayDeclNode : public VarDeclNode {
public:
    int size;
    
    ArrayDeclNode(const std::string& t, const std::string& n, int s)
        : VarDeclNode(t, n), size(s) {}
    
    void generate_code() const override {
        std::string promela_type = get_promela_type(type);
        std::cout << promela_type << " " << name << "[" << size << "];\n";
    }
};

#endif // AST_H