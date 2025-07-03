/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 7 "parser.y"

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


#line 140 "parser.tab.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "parser.tab.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_INT = 3,                        /* INT  */
  YYSYMBOL_FLOAT = 4,                      /* FLOAT  */
  YYSYMBOL_DOUBLE = 5,                     /* DOUBLE  */
  YYSYMBOL_CHAR = 6,                       /* CHAR  */
  YYSYMBOL_IF = 7,                         /* IF  */
  YYSYMBOL_ELSE = 8,                       /* ELSE  */
  YYSYMBOL_WHILE = 9,                      /* WHILE  */
  YYSYMBOL_RETURN = 10,                    /* RETURN  */
  YYSYMBOL_PRINTF = 11,                    /* PRINTF  */
  YYSYMBOL_CHAN = 12,                      /* CHAN  */
  YYSYMBOL_OF = 13,                        /* OF  */
  YYSYMBOL_NUMBER = 14,                    /* NUMBER  */
  YYSYMBOL_FLOAT_VAL = 15,                 /* FLOAT_VAL  */
  YYSYMBOL_IDENTIFIER = 16,                /* IDENTIFIER  */
  YYSYMBOL_STRING_LITERAL = 17,            /* STRING_LITERAL  */
  YYSYMBOL_CHAR_VAL = 18,                  /* CHAR_VAL  */
  YYSYMBOL_EQ = 19,                        /* EQ  */
  YYSYMBOL_NE = 20,                        /* NE  */
  YYSYMBOL_LE = 21,                        /* LE  */
  YYSYMBOL_GE = 22,                        /* GE  */
  YYSYMBOL_AND = 23,                       /* AND  */
  YYSYMBOL_OR = 24,                        /* OR  */
  YYSYMBOL_25_ = 25,                       /* '<'  */
  YYSYMBOL_26_ = 26,                       /* '>'  */
  YYSYMBOL_27_ = 27,                       /* '+'  */
  YYSYMBOL_28_ = 28,                       /* '-'  */
  YYSYMBOL_29_ = 29,                       /* '*'  */
  YYSYMBOL_30_ = 30,                       /* '/'  */
  YYSYMBOL_31_ = 31,                       /* '%'  */
  YYSYMBOL_UMINUS = 32,                    /* UMINUS  */
  YYSYMBOL_33_ = 33,                       /* '!'  */
  YYSYMBOL_IF_WITHOUT_ELSE = 34,           /* IF_WITHOUT_ELSE  */
  YYSYMBOL_35_ = 35,                       /* ';'  */
  YYSYMBOL_36_ = 36,                       /* '['  */
  YYSYMBOL_37_ = 37,                       /* ']'  */
  YYSYMBOL_38_ = 38,                       /* '='  */
  YYSYMBOL_39_ = 39,                       /* '('  */
  YYSYMBOL_40_ = 40,                       /* ')'  */
  YYSYMBOL_41_ = 41,                       /* ','  */
  YYSYMBOL_42_ = 42,                       /* '{'  */
  YYSYMBOL_43_ = 43,                       /* '}'  */
  YYSYMBOL_YYACCEPT = 44,                  /* $accept  */
  YYSYMBOL_program = 45,                   /* program  */
  YYSYMBOL_declaration_list = 46,          /* declaration_list  */
  YYSYMBOL_declaration = 47,               /* declaration  */
  YYSYMBOL_variable_declaration = 48,      /* variable_declaration  */
  YYSYMBOL_function_definition = 49,       /* function_definition  */
  YYSYMBOL_50_1 = 50,                      /* $@1  */
  YYSYMBOL_51_2 = 51,                      /* $@2  */
  YYSYMBOL_52_3 = 52,                      /* $@3  */
  YYSYMBOL_53_4 = 53,                      /* $@4  */
  YYSYMBOL_54_5 = 54,                      /* $@5  */
  YYSYMBOL_55_6 = 55,                      /* $@6  */
  YYSYMBOL_56_7 = 56,                      /* $@7  */
  YYSYMBOL_57_8 = 57,                      /* $@8  */
  YYSYMBOL_parameter_list = 58,            /* parameter_list  */
  YYSYMBOL_parameter = 59,                 /* parameter  */
  YYSYMBOL_compound_statement = 60,        /* compound_statement  */
  YYSYMBOL_61_9 = 61,                      /* @9  */
  YYSYMBOL_statement_list = 62,            /* statement_list  */
  YYSYMBOL_statement = 63,                 /* statement  */
  YYSYMBOL_expression_statement = 64,      /* expression_statement  */
  YYSYMBOL_selection_statement = 65,       /* selection_statement  */
  YYSYMBOL_iteration_statement = 66,       /* iteration_statement  */
  YYSYMBOL_printf_statement = 67,          /* printf_statement  */
  YYSYMBOL_return_statement = 68,          /* return_statement  */
  YYSYMBOL_argument_list = 69,             /* argument_list  */
  YYSYMBOL_expression = 70,                /* expression  */
  YYSYMBOL_assignment_expression = 71,     /* assignment_expression  */
  YYSYMBOL_logical_or_expression = 72,     /* logical_or_expression  */
  YYSYMBOL_logical_and_expression = 73,    /* logical_and_expression  */
  YYSYMBOL_equality_expression = 74,       /* equality_expression  */
  YYSYMBOL_relational_expression = 75,     /* relational_expression  */
  YYSYMBOL_additive_expression = 76,       /* additive_expression  */
  YYSYMBOL_multiplicative_expression = 77, /* multiplicative_expression  */
  YYSYMBOL_unary_expression = 78,          /* unary_expression  */
  YYSYMBOL_postfix_expression = 79,        /* postfix_expression  */
  YYSYMBOL_primary_expression = 80         /* primary_expression  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_uint8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
# define YYCOPY_NEEDED 1
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  14
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   249

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  44
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  37
/* YYNRULES -- Number of rules.  */
#define YYNRULES  96
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  198

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   281


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    33,     2,     2,     2,    31,     2,     2,
      39,    40,    29,    27,    41,    28,     2,    30,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,    35,
      25,    38,    26,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    36,     2,    37,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    42,     2,    43,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      32,    34
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   154,   154,   166,   171,   179,   183,   191,   197,   205,
     211,   217,   223,   229,   235,   241,   247,   253,   263,   262,
     279,   278,   295,   294,   311,   310,   327,   326,   339,   338,
     351,   350,   363,   362,   378,   384,   393,   398,   403,   408,
     417,   416,   431,   439,   444,   452,   456,   460,   464,   468,
     472,   476,   483,   488,   496,   502,   511,   520,   526,   537,
     542,   550,   555,   563,   570,   574,   606,   610,   618,   622,
     630,   634,   639,   647,   651,   656,   661,   666,   674,   678,
     683,   691,   695,   700,   705,   713,   717,   722,   731,   735,
     741,   747,   760,   766,   771,   776,   781
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "INT", "FLOAT",
  "DOUBLE", "CHAR", "IF", "ELSE", "WHILE", "RETURN", "PRINTF", "CHAN",
  "OF", "NUMBER", "FLOAT_VAL", "IDENTIFIER", "STRING_LITERAL", "CHAR_VAL",
  "EQ", "NE", "LE", "GE", "AND", "OR", "'<'", "'>'", "'+'", "'-'", "'*'",
  "'/'", "'%'", "UMINUS", "'!'", "IF_WITHOUT_ELSE", "';'", "'['", "']'",
  "'='", "'('", "')'", "','", "'{'", "'}'", "$accept", "program",
  "declaration_list", "declaration", "variable_declaration",
  "function_definition", "$@1", "$@2", "$@3", "$@4", "$@5", "$@6", "$@7",
  "$@8", "parameter_list", "parameter", "compound_statement", "@9",
  "statement_list", "statement", "expression_statement",
  "selection_statement", "iteration_statement", "printf_statement",
  "return_statement", "argument_list", "expression",
  "assignment_expression", "logical_or_expression",
  "logical_and_expression", "equality_expression", "relational_expression",
  "additive_expression", "multiplicative_expression", "unary_expression",
  "postfix_expression", "primary_expression", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-155)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
      32,   -10,    -2,    45,    53,    91,    32,  -155,  -155,  -155,
      84,   -23,    28,   106,  -155,  -155,  -155,    70,    14,  -155,
     103,   158,   109,  -155,   107,   158,   123,  -155,   120,   158,
     127,    59,    89,   143,   148,   153,  -155,   -12,  -155,   102,
    -155,  -155,   104,  -155,   158,   158,   158,   136,  -155,   156,
     173,    60,    82,   124,   117,  -155,    19,  -155,  -155,   125,
     175,   159,  -155,   138,   178,   165,  -155,   162,   181,  -155,
    -155,  -155,  -155,   177,  -155,   179,   185,   122,  -155,   186,
    -155,   183,  -155,   158,   158,   158,   158,   158,   158,   158,
     158,   158,   158,   158,   158,   158,   158,   158,   177,  -155,
     189,  -155,   177,  -155,   190,  -155,   177,  -155,  -155,   184,
    -155,   177,  -155,  -155,  -155,   164,  -155,  -155,   173,    60,
      82,    82,   124,   124,   124,   124,   117,   117,  -155,  -155,
    -155,   191,  -155,  -155,   177,  -155,  -155,   177,  -155,  -155,
     177,  -155,    83,  -155,  -155,   158,  -155,  -155,  -155,  -155,
     205,   210,   213,   214,   192,   193,   142,   194,  -155,  -155,
    -155,    67,  -155,  -155,  -155,  -155,  -155,  -155,   199,  -155,
     171,   -14,   157,   163,   158,   158,  -155,   200,   219,  -155,
    -155,  -155,   197,   198,  -155,   168,    83,    83,   204,   158,
     232,  -155,  -155,   170,    83,   206,  -155,  -155
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,     0,     0,     0,     0,     0,     2,     3,     5,     6,
       0,     0,     0,     0,     1,     4,     7,     0,     0,     9,
       0,     0,     0,    12,     0,     0,     0,    15,     0,     0,
       0,     0,     0,     0,     0,     0,    26,     0,    34,     0,
      93,    94,    92,    95,     0,     0,     0,     0,    63,    64,
      66,    68,    70,    73,    78,    81,    85,    88,    28,     0,
       0,     0,    30,     0,     0,     0,    32,     0,     0,    36,
      37,    38,    39,     0,    18,     0,     0,     0,    86,    85,
      87,     0,    10,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    20,
       0,    13,     0,    22,     0,    16,     0,    24,     8,    40,
      27,     0,    35,    11,    90,     0,    61,    96,    67,    69,
      71,    72,    76,    77,    74,    75,    79,    80,    82,    83,
      84,     0,    65,    29,     0,    14,    31,     0,    17,    33,
       0,    42,     0,    19,    91,     0,    89,    21,    23,    25,
       0,     0,     0,     0,     0,     0,     0,     0,    52,    51,
      46,     0,    43,    45,    47,    48,    49,    50,     0,    62,
       0,     0,     0,     0,     0,     0,    60,     0,     0,    41,
      44,    53,     0,     0,    59,     0,     0,     0,     0,     0,
      54,    56,    57,     0,     0,     0,    55,    58
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -155,  -155,  -155,   236,     5,  -155,  -155,  -155,  -155,  -155,
    -155,  -155,  -155,  -155,     1,   169,   -72,  -155,  -155,  -154,
    -155,  -155,  -155,  -155,  -155,    54,   -21,   149,  -155,   166,
     161,   128,   100,   126,   -35,   -42,  -155
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_uint8 yydefgoto[] =
{
       0,     5,     6,     7,   159,     9,   111,   134,   137,   140,
      73,    98,   102,   106,    37,    38,   160,   142,   161,   162,
     163,   164,   165,   166,   167,   115,   168,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      47,   110,    79,    79,    61,     8,    10,   180,    65,    78,
      80,     8,    19,    20,    11,    21,    22,    32,    33,    34,
      35,    19,    20,    59,    21,    81,   133,    63,    74,    75,
     136,    67,   190,   191,   139,     1,     2,     3,     4,   143,
     196,    79,    79,    79,    79,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    36,    96,   116,    97,   128,   129,
     130,    12,   147,    23,    24,   148,    25,    26,   149,    13,
     150,   151,   152,   153,   154,   131,   155,   156,   157,    85,
      86,    40,    41,    42,    31,    43,   150,   151,   152,   153,
     154,    14,   155,   156,   157,    44,    68,    40,    41,    42,
      45,    43,   158,    87,    88,    69,    46,    89,    90,   109,
     179,    44,    32,    33,    34,    35,    45,    39,   158,    16,
      17,    60,    46,    18,   169,   109,    32,    33,    34,    35,
      32,    33,    34,    35,    64,   177,    40,    41,    42,    76,
      43,    27,    28,    77,    29,    30,    93,    94,    95,    58,
      44,    91,    92,   182,   183,    45,    40,    41,    42,    70,
      43,    46,   114,    62,    71,    99,    75,    66,   116,    72,
      44,    82,    40,    41,    42,    45,    43,   176,   103,    75,
      83,    46,    32,    33,    34,    35,    44,   122,   123,   124,
     125,    45,    23,    24,   101,    25,    84,    46,    27,    28,
     105,    29,   107,    75,   144,   145,    16,    17,   188,   189,
     195,   145,   100,   120,   121,   104,   108,   126,   127,   109,
     113,   170,    96,   117,   135,   138,   171,   141,   146,   172,
     173,   174,   175,   178,   181,   184,   185,   186,   187,   192,
     194,   197,    15,   193,   112,   119,   132,     0,     0,   118
};

static const yytype_int16 yycheck[] =
{
      21,    73,    44,    45,    25,     0,    16,   161,    29,    44,
      45,     6,    35,    36,    16,    38,    39,     3,     4,     5,
       6,    35,    36,    22,    38,    46,    98,    26,    40,    41,
     102,    30,   186,   187,   106,     3,     4,     5,     6,   111,
     194,    83,    84,    85,    86,    87,    88,    89,    90,    91,
      92,    93,    94,    95,    40,    36,    77,    38,    93,    94,
      95,    16,   134,    35,    36,   137,    38,    39,   140,    16,
       3,     4,     5,     6,     7,    96,     9,    10,    11,    19,
      20,    14,    15,    16,    14,    18,     3,     4,     5,     6,
       7,     0,     9,    10,    11,    28,    37,    14,    15,    16,
      33,    18,    35,    21,    22,    16,    39,    25,    26,    42,
      43,    28,     3,     4,     5,     6,    33,    14,    35,    35,
      36,    14,    39,    39,   145,    42,     3,     4,     5,     6,
       3,     4,     5,     6,    14,   156,    14,    15,    16,    37,
      18,    35,    36,    39,    38,    39,    29,    30,    31,    40,
      28,    27,    28,   174,   175,    33,    14,    15,    16,    16,
      18,    39,    40,    40,    16,    40,    41,    40,   189,    16,
      28,    35,    14,    15,    16,    33,    18,    35,    40,    41,
      24,    39,     3,     4,     5,     6,    28,    87,    88,    89,
      90,    33,    35,    36,    35,    38,    23,    39,    35,    36,
      35,    38,    40,    41,    40,    41,    35,    36,    40,    41,
      40,    41,    37,    85,    86,    37,    35,    91,    92,    42,
      35,    16,    36,    40,    35,    35,    16,    43,    37,    16,
      16,    39,    39,    39,    35,    35,    17,    40,    40,    35,
       8,    35,     6,   189,    75,    84,    97,    -1,    -1,    83
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     3,     4,     5,     6,    45,    46,    47,    48,    49,
      16,    16,    16,    16,     0,    47,    35,    36,    39,    35,
      36,    38,    39,    35,    36,    38,    39,    35,    36,    38,
      39,    14,     3,     4,     5,     6,    40,    58,    59,    14,
      14,    15,    16,    18,    28,    33,    39,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    80,    40,    58,
      14,    70,    40,    58,    14,    70,    40,    58,    37,    16,
      16,    16,    16,    54,    40,    41,    37,    39,    78,    79,
      78,    70,    35,    24,    23,    19,    20,    21,    22,    25,
      26,    27,    28,    29,    30,    31,    36,    38,    55,    40,
      37,    35,    56,    40,    37,    35,    57,    40,    35,    42,
      60,    50,    59,    35,    40,    69,    70,    40,    73,    74,
      75,    75,    76,    76,    76,    76,    77,    77,    78,    78,
      78,    70,    71,    60,    51,    35,    60,    52,    35,    60,
      53,    43,    61,    60,    40,    41,    37,    60,    60,    60,
       3,     4,     5,     6,     7,     9,    10,    11,    35,    48,
      60,    62,    63,    64,    65,    66,    67,    68,    70,    70,
      16,    16,    16,    16,    39,    39,    35,    70,    39,    43,
      63,    35,    70,    70,    35,    17,    40,    40,    40,    41,
      63,    63,    35,    69,     8,    40,    63,    35
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    44,    45,    46,    46,    47,    47,    48,    48,    48,
      48,    48,    48,    48,    48,    48,    48,    48,    50,    49,
      51,    49,    52,    49,    53,    49,    54,    49,    55,    49,
      56,    49,    57,    49,    58,    58,    59,    59,    59,    59,
      61,    60,    60,    62,    62,    63,    63,    63,    63,    63,
      63,    63,    64,    64,    65,    65,    66,    67,    67,    68,
      68,    69,    69,    70,    71,    71,    72,    72,    73,    73,
      74,    74,    74,    75,    75,    75,    75,    75,    76,    76,
      76,    77,    77,    77,    77,    78,    78,    78,    79,    79,
      79,    79,    80,    80,    80,    80,    80
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     2,     1,     1,     3,     6,     3,
       5,     6,     3,     5,     6,     3,     5,     6,     0,     7,
       0,     7,     0,     7,     0,     7,     0,     6,     0,     6,
       0,     6,     0,     6,     1,     3,     2,     2,     2,     2,
       0,     4,     2,     1,     2,     1,     1,     1,     1,     1,
       1,     1,     1,     2,     5,     7,     5,     5,     7,     3,
       2,     1,     3,     1,     1,     3,     1,     3,     1,     3,
       1,     3,     3,     1,     3,     3,     3,     3,     1,     3,
       3,     1,     3,     3,     3,     1,     2,     2,     1,     4,
       3,     4,     1,     1,     1,     1,     3
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        YY_LAC_DISCARD ("YYBACKUP");                              \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)]);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


/* Given a state stack such that *YYBOTTOM is its bottom, such that
   *YYTOP is either its top or is YYTOP_EMPTY to indicate an empty
   stack, and such that *YYCAPACITY is the maximum number of elements it
   can hold without a reallocation, make sure there is enough room to
   store YYADD more elements.  If not, allocate a new stack using
   YYSTACK_ALLOC, copy the existing elements, and adjust *YYBOTTOM,
   *YYTOP, and *YYCAPACITY to reflect the new capacity and memory
   location.  If *YYBOTTOM != YYBOTTOM_NO_FREE, then free the old stack
   using YYSTACK_FREE.  Return 0 if successful or if no reallocation is
   required.  Return YYENOMEM if memory is exhausted.  */
static int
yy_lac_stack_realloc (YYPTRDIFF_T *yycapacity, YYPTRDIFF_T yyadd,
#if YYDEBUG
                      char const *yydebug_prefix,
                      char const *yydebug_suffix,
#endif
                      yy_state_t **yybottom,
                      yy_state_t *yybottom_no_free,
                      yy_state_t **yytop, yy_state_t *yytop_empty)
{
  YYPTRDIFF_T yysize_old =
    *yytop == yytop_empty ? 0 : *yytop - *yybottom + 1;
  YYPTRDIFF_T yysize_new = yysize_old + yyadd;
  if (*yycapacity < yysize_new)
    {
      YYPTRDIFF_T yyalloc = 2 * yysize_new;
      yy_state_t *yybottom_new;
      /* Use YYMAXDEPTH for maximum stack size given that the stack
         should never need to grow larger than the main state stack
         needs to grow without LAC.  */
      if (YYMAXDEPTH < yysize_new)
        {
          YYDPRINTF ((stderr, "%smax size exceeded%s", yydebug_prefix,
                      yydebug_suffix));
          return YYENOMEM;
        }
      if (YYMAXDEPTH < yyalloc)
        yyalloc = YYMAXDEPTH;
      yybottom_new =
        YY_CAST (yy_state_t *,
                 YYSTACK_ALLOC (YY_CAST (YYSIZE_T,
                                         yyalloc * YYSIZEOF (*yybottom_new))));
      if (!yybottom_new)
        {
          YYDPRINTF ((stderr, "%srealloc failed%s", yydebug_prefix,
                      yydebug_suffix));
          return YYENOMEM;
        }
      if (*yytop != yytop_empty)
        {
          YYCOPY (yybottom_new, *yybottom, yysize_old);
          *yytop = yybottom_new + (yysize_old - 1);
        }
      if (*yybottom != yybottom_no_free)
        YYSTACK_FREE (*yybottom);
      *yybottom = yybottom_new;
      *yycapacity = yyalloc;
    }
  return 0;
}

/* Establish the initial context for the current lookahead if no initial
   context is currently established.

   We define a context as a snapshot of the parser stacks.  We define
   the initial context for a lookahead as the context in which the
   parser initially examines that lookahead in order to select a
   syntactic action.  Thus, if the lookahead eventually proves
   syntactically unacceptable (possibly in a later context reached via a
   series of reductions), the initial context can be used to determine
   the exact set of tokens that would be syntactically acceptable in the
   lookahead's place.  Moreover, it is the context after which any
   further semantic actions would be erroneous because they would be
   determined by a syntactically unacceptable token.

   YY_LAC_ESTABLISH should be invoked when a reduction is about to be
   performed in an inconsistent state (which, for the purposes of LAC,
   includes consistent states that don't know they're consistent because
   their default reductions have been disabled).  Iff there is a
   lookahead token, it should also be invoked before reporting a syntax
   error.  This latter case is for the sake of the debugging output.

   For parse.lac=full, the implementation of YY_LAC_ESTABLISH is as
   follows.  If no initial context is currently established for the
   current lookahead, then check if that lookahead can eventually be
   shifted if syntactic actions continue from the current context.
   Report a syntax error if it cannot.  */
#define YY_LAC_ESTABLISH                                                \
do {                                                                    \
  if (!yy_lac_established)                                              \
    {                                                                   \
      YYDPRINTF ((stderr,                                               \
                  "LAC: initial context established for %s\n",          \
                  yysymbol_name (yytoken)));                            \
      yy_lac_established = 1;                                           \
      switch (yy_lac (yyesa, &yyes, &yyes_capacity, yyssp, yytoken))    \
        {                                                               \
        case YYENOMEM:                                                  \
          YYNOMEM;                                                      \
        case 1:                                                         \
          goto yyerrlab;                                                \
        }                                                               \
    }                                                                   \
} while (0)

/* Discard any previous initial lookahead context because of Event,
   which may be a lookahead change or an invalidation of the currently
   established initial context for the current lookahead.

   The most common example of a lookahead change is a shift.  An example
   of both cases is syntax error recovery.  That is, a syntax error
   occurs when the lookahead is syntactically erroneous for the
   currently established initial context, so error recovery manipulates
   the parser stacks to try to find a new initial context in which the
   current lookahead is syntactically acceptable.  If it fails to find
   such a context, it discards the lookahead.  */
#if YYDEBUG
# define YY_LAC_DISCARD(Event)                                           \
do {                                                                     \
  if (yy_lac_established)                                                \
    {                                                                    \
      YYDPRINTF ((stderr, "LAC: initial context discarded due to "       \
                  Event "\n"));                                          \
      yy_lac_established = 0;                                            \
    }                                                                    \
} while (0)
#else
# define YY_LAC_DISCARD(Event) yy_lac_established = 0
#endif

/* Given the stack whose top is *YYSSP, return 0 iff YYTOKEN can
   eventually (after perhaps some reductions) be shifted, return 1 if
   not, or return YYENOMEM if memory is exhausted.  As preconditions and
   postconditions: *YYES_CAPACITY is the allocated size of the array to
   which *YYES points, and either *YYES = YYESA or *YYES points to an
   array allocated with YYSTACK_ALLOC.  yy_lac may overwrite the
   contents of either array, alter *YYES and *YYES_CAPACITY, and free
   any old *YYES other than YYESA.  */
static int
yy_lac (yy_state_t *yyesa, yy_state_t **yyes,
        YYPTRDIFF_T *yyes_capacity, yy_state_t *yyssp, yysymbol_kind_t yytoken)
{
  yy_state_t *yyes_prev = yyssp;
  yy_state_t *yyesp = yyes_prev;
  /* Reduce until we encounter a shift and thereby accept the token.  */
  YYDPRINTF ((stderr, "LAC: checking lookahead %s:", yysymbol_name (yytoken)));
  if (yytoken == YYSYMBOL_YYUNDEF)
    {
      YYDPRINTF ((stderr, " Always Err\n"));
      return 1;
    }
  while (1)
    {
      int yyrule = yypact[+*yyesp];
      if (yypact_value_is_default (yyrule)
          || (yyrule += yytoken) < 0 || YYLAST < yyrule
          || yycheck[yyrule] != yytoken)
        {
          /* Use the default action.  */
          yyrule = yydefact[+*yyesp];
          if (yyrule == 0)
            {
              YYDPRINTF ((stderr, " Err\n"));
              return 1;
            }
        }
      else
        {
          /* Use the action from yytable.  */
          yyrule = yytable[yyrule];
          if (yytable_value_is_error (yyrule))
            {
              YYDPRINTF ((stderr, " Err\n"));
              return 1;
            }
          if (0 < yyrule)
            {
              YYDPRINTF ((stderr, " S%d\n", yyrule));
              return 0;
            }
          yyrule = -yyrule;
        }
      /* By now we know we have to simulate a reduce.  */
      YYDPRINTF ((stderr, " R%d", yyrule - 1));
      {
        /* Pop the corresponding number of values from the stack.  */
        YYPTRDIFF_T yylen = yyr2[yyrule];
        /* First pop from the LAC stack as many tokens as possible.  */
        if (yyesp != yyes_prev)
          {
            YYPTRDIFF_T yysize = yyesp - *yyes + 1;
            if (yylen < yysize)
              {
                yyesp -= yylen;
                yylen = 0;
              }
            else
              {
                yyesp = yyes_prev;
                yylen -= yysize;
              }
          }
        /* Only afterwards look at the main stack.  */
        if (yylen)
          yyesp = yyes_prev -= yylen;
      }
      /* Push the resulting state of the reduction.  */
      {
        yy_state_fast_t yystate;
        {
          const int yylhs = yyr1[yyrule] - YYNTOKENS;
          const int yyi = yypgoto[yylhs] + *yyesp;
          yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyesp
                     ? yytable[yyi]
                     : yydefgoto[yylhs]);
        }
        if (yyesp == yyes_prev)
          {
            yyesp = *yyes;
            YY_IGNORE_USELESS_CAST_BEGIN
            *yyesp = YY_CAST (yy_state_t, yystate);
            YY_IGNORE_USELESS_CAST_END
          }
        else
          {
            if (yy_lac_stack_realloc (yyes_capacity, 1,
#if YYDEBUG
                                      " (", ")",
#endif
                                      yyes, yyesa, &yyesp, yyes_prev))
              {
                YYDPRINTF ((stderr, "\n"));
                return YYENOMEM;
              }
            YY_IGNORE_USELESS_CAST_BEGIN
            *++yyesp = YY_CAST (yy_state_t, yystate);
            YY_IGNORE_USELESS_CAST_END
          }
        YYDPRINTF ((stderr, " G%d", yystate));
      }
    }
}

/* Context of a parse error.  */
typedef struct
{
  yy_state_t *yyssp;
  yy_state_t *yyesa;
  yy_state_t **yyes;
  YYPTRDIFF_T *yyes_capacity;
  yysymbol_kind_t yytoken;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;

  int yyx;
  for (yyx = 0; yyx < YYNTOKENS; ++yyx)
    {
      yysymbol_kind_t yysym = YY_CAST (yysymbol_kind_t, yyx);
      if (yysym != YYSYMBOL_YYerror && yysym != YYSYMBOL_YYUNDEF)
        switch (yy_lac (yyctx->yyesa, yyctx->yyes, yyctx->yyes_capacity, yyctx->yyssp, yysym))
          {
          case YYENOMEM:
            return YYENOMEM;
          case 1:
            continue;
          default:
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = yysym;
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}




#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;
      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
       In the first two cases, it might appear that the current syntax
       error should have been detected in the previous state when yy_lac
       was invoked.  However, at that time, there might have been a
       different syntax error that discarded a different initial context
       during error recovery, leaving behind the current lookahead.
  */
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      YYDPRINTF ((stderr, "Constructing syntax error message\n"));
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else if (yyn == 0)
        YYDPRINTF ((stderr, "No expected tokens.\n"));
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.  In order to see if a particular token T is a
   valid looakhead, invoke yy_lac (YYESA, YYES, YYES_CAPACITY, YYSSP, T).

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store or if
   yy_lac returned YYENOMEM.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep)
{
  YY_USE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/* Lookahead token kind.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

    yy_state_t yyesa[20];
    yy_state_t *yyes = yyesa;
    YYPTRDIFF_T yyes_capacity = 20 < YYMAXDEPTH ? 20 : YYMAXDEPTH;

  /* Whether LAC context is established.  A Boolean.  */
  int yy_lac_established = 0;
  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    {
      YY_LAC_ESTABLISH;
      goto yydefault;
    }
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      YY_LAC_ESTABLISH;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  YY_LAC_DISCARD ("shift");
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  {
    int yychar_backup = yychar;
    switch (yyn)
      {
  case 2: /* program: declaration_list  */
#line 155 "parser.y"
        {
            auto prog = new ProgramNode();
            prog->declarations = *(yyvsp[0].node_list);
            (yyval.program) = prog;
            root = prog;
            register_node(prog);
            delete (yyvsp[0].node_list);
        }
#line 1862 "parser.tab.c"
    break;

  case 3: /* declaration_list: declaration  */
#line 167 "parser.y"
        {
            (yyval.node_list) = new std::vector<ASTNode*>();
            if ((yyvsp[0].node)) (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 1871 "parser.tab.c"
    break;

  case 4: /* declaration_list: declaration_list declaration  */
#line 172 "parser.y"
        {
            (yyval.node_list) = (yyvsp[-1].node_list);
            if ((yyvsp[0].node)) (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 1880 "parser.tab.c"
    break;

  case 5: /* declaration: variable_declaration  */
#line 180 "parser.y"
        {
            (yyval.node) = (yyvsp[0].var_decl);
        }
#line 1888 "parser.tab.c"
    break;

  case 6: /* declaration: function_definition  */
#line 184 "parser.y"
        {
            (yyval.node) = (yyvsp[0].func_decl);
        }
#line 1896 "parser.tab.c"
    break;

  case 7: /* variable_declaration: INT IDENTIFIER ';'  */
#line 192 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("int", (yyvsp[-1].id));
            register_node((yyval.var_decl));
            free((yyvsp[-1].id));
        }
#line 1906 "parser.tab.c"
    break;

  case 8: /* variable_declaration: INT IDENTIFIER '[' NUMBER ']' ';'  */
#line 198 "parser.y"
        {
            // Create array declaration
            (yyval.var_decl) = new VarDeclNode("int", (yyvsp[-4].id), (yyvsp[-2].num));
            (yyval.var_decl)->arraySize = (yyvsp[-2].num);  // Set array size
            register_node((yyval.var_decl));
            free((yyvsp[-4].id));
        }
#line 1918 "parser.tab.c"
    break;

  case 9: /* variable_declaration: FLOAT IDENTIFIER ';'  */
#line 206 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("float", (yyvsp[-1].id));
            register_node((yyval.var_decl));
            free((yyvsp[-1].id));
        }
#line 1928 "parser.tab.c"
    break;

  case 10: /* variable_declaration: FLOAT IDENTIFIER '=' expression ';'  */
#line 212 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("float", (yyvsp[-3].id), (yyvsp[-1].node));
            register_node((yyval.var_decl));
            free((yyvsp[-3].id));
        }
#line 1938 "parser.tab.c"
    break;

  case 11: /* variable_declaration: FLOAT IDENTIFIER '[' NUMBER ']' ';'  */
#line 218 "parser.y"
        {
            (yyval.var_decl) = new ArrayDeclNode("float", (yyvsp[-4].id), (yyvsp[-2].num));
            register_node((yyval.var_decl));
            free((yyvsp[-4].id));
        }
#line 1948 "parser.tab.c"
    break;

  case 12: /* variable_declaration: DOUBLE IDENTIFIER ';'  */
#line 224 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("double", (yyvsp[-1].id));
            register_node((yyval.var_decl));
            free((yyvsp[-1].id));
        }
#line 1958 "parser.tab.c"
    break;

  case 13: /* variable_declaration: DOUBLE IDENTIFIER '=' expression ';'  */
#line 230 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("double", (yyvsp[-3].id), (yyvsp[-1].node));
            register_node((yyval.var_decl));
            free((yyvsp[-3].id));
        }
#line 1968 "parser.tab.c"
    break;

  case 14: /* variable_declaration: DOUBLE IDENTIFIER '[' NUMBER ']' ';'  */
#line 236 "parser.y"
        {
            (yyval.var_decl) = new ArrayDeclNode("double", (yyvsp[-4].id), (yyvsp[-2].num));
            register_node((yyval.var_decl));
            free((yyvsp[-4].id));
        }
#line 1978 "parser.tab.c"
    break;

  case 15: /* variable_declaration: CHAR IDENTIFIER ';'  */
#line 242 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("char", (yyvsp[-1].id));
            register_node((yyval.var_decl));
            free((yyvsp[-1].id));
        }
#line 1988 "parser.tab.c"
    break;

  case 16: /* variable_declaration: CHAR IDENTIFIER '=' expression ';'  */
#line 248 "parser.y"
        {
            (yyval.var_decl) = new VarDeclNode("char", (yyvsp[-3].id), (yyvsp[-1].node));
            register_node((yyval.var_decl));
            free((yyvsp[-3].id));
        }
#line 1998 "parser.tab.c"
    break;

  case 17: /* variable_declaration: CHAR IDENTIFIER '[' NUMBER ']' ';'  */
#line 254 "parser.y"
        {
            (yyval.var_decl) = new ArrayDeclNode("char", (yyvsp[-4].id), (yyvsp[-2].num));
            register_node((yyval.var_decl));
            free((yyvsp[-4].id));
        }
#line 2008 "parser.tab.c"
    break;

  case 18: /* $@1: %empty  */
#line 263 "parser.y"
        {
            current_function_name = (yyvsp[-3].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("int", (yyvsp[-3].id)));
        }
#line 2018 "parser.tab.c"
    break;

  case 19: /* function_definition: INT IDENTIFIER '(' parameter_list ')' $@1 compound_statement  */
#line 269 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("int", (yyvsp[-5].id), (yyvsp[0].compound_stmt));
            if ((yyvsp[-3].param_list)) {
                (yyval.func_decl)->parameters = *(yyvsp[-3].param_list);
                delete (yyvsp[-3].param_list);
            }
            register_node((yyval.func_decl));
            free((yyvsp[-5].id));
        }
#line 2032 "parser.tab.c"
    break;

  case 20: /* $@2: %empty  */
#line 279 "parser.y"
        {
            current_function_name = (yyvsp[-3].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("float", (yyvsp[-3].id)));
        }
#line 2042 "parser.tab.c"
    break;

  case 21: /* function_definition: FLOAT IDENTIFIER '(' parameter_list ')' $@2 compound_statement  */
#line 285 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("float", (yyvsp[-5].id), (yyvsp[0].compound_stmt));
            if ((yyvsp[-3].param_list)) {
                (yyval.func_decl)->parameters = *(yyvsp[-3].param_list);
                delete (yyvsp[-3].param_list);
            }
            register_node((yyval.func_decl));
            free((yyvsp[-5].id));
        }
#line 2056 "parser.tab.c"
    break;

  case 22: /* $@3: %empty  */
#line 295 "parser.y"
        {
            current_function_name = (yyvsp[-3].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("double", (yyvsp[-3].id)));
        }
#line 2066 "parser.tab.c"
    break;

  case 23: /* function_definition: DOUBLE IDENTIFIER '(' parameter_list ')' $@3 compound_statement  */
#line 301 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("double", (yyvsp[-5].id), (yyvsp[0].compound_stmt));
            if ((yyvsp[-3].param_list)) {
                (yyval.func_decl)->parameters = *(yyvsp[-3].param_list);
                delete (yyvsp[-3].param_list);
            }
            register_node((yyval.func_decl));
            free((yyvsp[-5].id));
        }
#line 2080 "parser.tab.c"
    break;

  case 24: /* $@4: %empty  */
#line 311 "parser.y"
        {
            current_function_name = (yyvsp[-3].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("char", (yyvsp[-3].id)));
        }
#line 2090 "parser.tab.c"
    break;

  case 25: /* function_definition: CHAR IDENTIFIER '(' parameter_list ')' $@4 compound_statement  */
#line 317 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("char", (yyvsp[-5].id), (yyvsp[0].compound_stmt));
            if ((yyvsp[-3].param_list)) {
                (yyval.func_decl)->parameters = *(yyvsp[-3].param_list);
                delete (yyvsp[-3].param_list);
            }
            register_node((yyval.func_decl));
            free((yyvsp[-5].id));
        }
#line 2104 "parser.tab.c"
    break;

  case 26: /* $@5: %empty  */
#line 327 "parser.y"
        {
            current_function_name = (yyvsp[-2].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("int", (yyvsp[-2].id)));
        }
#line 2114 "parser.tab.c"
    break;

  case 27: /* function_definition: INT IDENTIFIER '(' ')' $@5 compound_statement  */
#line 333 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("int", (yyvsp[-4].id), (yyvsp[0].compound_stmt));
            register_node((yyval.func_decl));
            free((yyvsp[-4].id));
        }
#line 2124 "parser.tab.c"
    break;

  case 28: /* $@6: %empty  */
#line 339 "parser.y"
        {
            current_function_name = (yyvsp[-2].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("float", (yyvsp[-2].id)));
        }
#line 2134 "parser.tab.c"
    break;

  case 29: /* function_definition: FLOAT IDENTIFIER '(' ')' $@6 compound_statement  */
#line 345 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("float", (yyvsp[-4].id), (yyvsp[0].compound_stmt));
            register_node((yyval.func_decl));
            free((yyvsp[-4].id));
        }
#line 2144 "parser.tab.c"
    break;

  case 30: /* $@7: %empty  */
#line 351 "parser.y"
        {
            current_function_name = (yyvsp[-2].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("double", (yyvsp[-2].id)));
        }
#line 2154 "parser.tab.c"
    break;

  case 31: /* function_definition: DOUBLE IDENTIFIER '(' ')' $@7 compound_statement  */
#line 357 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("double", (yyvsp[-4].id), (yyvsp[0].compound_stmt));
            register_node((yyval.func_decl));
            free((yyvsp[-4].id));
        }
#line 2164 "parser.tab.c"
    break;

  case 32: /* $@8: %empty  */
#line 363 "parser.y"
        {
            current_function_name = (yyvsp[-2].id);
            // Record function return type for global variable generation
            function_returns.push_back(std::make_pair("char", (yyvsp[-2].id)));
        }
#line 2174 "parser.tab.c"
    break;

  case 33: /* function_definition: CHAR IDENTIFIER '(' ')' $@8 compound_statement  */
#line 369 "parser.y"
        {
            (yyval.func_decl) = new FunctionNode("char", (yyvsp[-4].id), (yyvsp[0].compound_stmt));
            register_node((yyval.func_decl));
            free((yyvsp[-4].id));
        }
#line 2184 "parser.tab.c"
    break;

  case 34: /* parameter_list: parameter  */
#line 379 "parser.y"
        {
            (yyval.param_list) = new std::vector<std::pair<std::string, std::string>>();
            (yyval.param_list)->push_back(*(yyvsp[0].param));
            delete (yyvsp[0].param);
        }
#line 2194 "parser.tab.c"
    break;

  case 35: /* parameter_list: parameter_list ',' parameter  */
#line 385 "parser.y"
        {
            (yyval.param_list) = (yyvsp[-2].param_list);
            (yyval.param_list)->push_back(*(yyvsp[0].param));
            delete (yyvsp[0].param);
        }
#line 2204 "parser.tab.c"
    break;

  case 36: /* parameter: INT IDENTIFIER  */
#line 394 "parser.y"
        {
            (yyval.param) = new std::pair<std::string, std::string>("int", (yyvsp[0].id));
            free((yyvsp[0].id));
        }
#line 2213 "parser.tab.c"
    break;

  case 37: /* parameter: FLOAT IDENTIFIER  */
#line 399 "parser.y"
        {
            (yyval.param) = new std::pair<std::string, std::string>("float", (yyvsp[0].id));
            free((yyvsp[0].id));
        }
#line 2222 "parser.tab.c"
    break;

  case 38: /* parameter: DOUBLE IDENTIFIER  */
#line 404 "parser.y"
        {
            (yyval.param) = new std::pair<std::string, std::string>("double", (yyvsp[0].id));
            free((yyvsp[0].id));
        }
#line 2231 "parser.tab.c"
    break;

  case 39: /* parameter: CHAR IDENTIFIER  */
#line 409 "parser.y"
        {
            (yyval.param) = new std::pair<std::string, std::string>("char", (yyvsp[0].id));
            free((yyvsp[0].id));
        }
#line 2240 "parser.tab.c"
    break;

  case 40: /* @9: %empty  */
#line 417 "parser.y"
        {
            // Use explicit type for mid-rule action
            (yyval.compound_stmt) = new CompoundStmtNode();
            register_node((yyval.compound_stmt));
        }
#line 2250 "parser.tab.c"
    break;

  case 41: /* compound_statement: '{' @9 statement_list '}'  */
#line 423 "parser.y"
        {
            // Reference the mid-rule action with proper type
            (yyval.compound_stmt) = (yyvsp[-2].compound_stmt);
            if ((yyvsp[-1].node_list)) {
                (yyval.compound_stmt)->statements = *(yyvsp[-1].node_list);
                delete (yyvsp[-1].node_list);
            }
        }
#line 2263 "parser.tab.c"
    break;

  case 42: /* compound_statement: '{' '}'  */
#line 432 "parser.y"
        {
            (yyval.compound_stmt) = new CompoundStmtNode();
            register_node((yyval.compound_stmt));
        }
#line 2272 "parser.tab.c"
    break;

  case 43: /* statement_list: statement  */
#line 440 "parser.y"
        {
            (yyval.node_list) = new std::vector<ASTNode*>();
            if ((yyvsp[0].node)) (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 2281 "parser.tab.c"
    break;

  case 44: /* statement_list: statement_list statement  */
#line 445 "parser.y"
        {
            (yyval.node_list) = (yyvsp[-1].node_list);
            if ((yyvsp[0].node)) (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 2290 "parser.tab.c"
    break;

  case 45: /* statement: expression_statement  */
#line 453 "parser.y"
        {
            (yyval.node) = (yyvsp[0].expr_stmt);
        }
#line 2298 "parser.tab.c"
    break;

  case 46: /* statement: compound_statement  */
#line 457 "parser.y"
        {
            (yyval.node) = (yyvsp[0].compound_stmt);
        }
#line 2306 "parser.tab.c"
    break;

  case 47: /* statement: selection_statement  */
#line 461 "parser.y"
        {
            (yyval.node) = (yyvsp[0].if_stmt);
        }
#line 2314 "parser.tab.c"
    break;

  case 48: /* statement: iteration_statement  */
#line 465 "parser.y"
        {
            (yyval.node) = (yyvsp[0].while_stmt);
        }
#line 2322 "parser.tab.c"
    break;

  case 49: /* statement: printf_statement  */
#line 469 "parser.y"
        {
            (yyval.node) = (yyvsp[0].printf_stmt);
        }
#line 2330 "parser.tab.c"
    break;

  case 50: /* statement: return_statement  */
#line 473 "parser.y"
        {
            (yyval.node) = (yyvsp[0].return_stmt);
        }
#line 2338 "parser.tab.c"
    break;

  case 51: /* statement: variable_declaration  */
#line 477 "parser.y"
        {
            (yyval.node) = (yyvsp[0].var_decl);
        }
#line 2346 "parser.tab.c"
    break;

  case 52: /* expression_statement: ';'  */
#line 484 "parser.y"
        {
            (yyval.expr_stmt) = new ExprStmtNode(nullptr);  // Empty statement
            register_node((yyval.expr_stmt));
        }
#line 2355 "parser.tab.c"
    break;

  case 53: /* expression_statement: expression ';'  */
#line 489 "parser.y"
        {
            (yyval.expr_stmt) = new ExprStmtNode((yyvsp[-1].node));
            register_node((yyval.expr_stmt));
        }
#line 2364 "parser.tab.c"
    break;

  case 54: /* selection_statement: IF '(' expression ')' statement  */
#line 497 "parser.y"
        {
            // Simple version - no buffer needed
            (yyval.if_stmt) = new IfStmtNode((yyvsp[-2].node), (yyvsp[0].node));
            register_node((yyval.if_stmt));
        }
#line 2374 "parser.tab.c"
    break;

  case 55: /* selection_statement: IF '(' expression ')' statement ELSE statement  */
#line 503 "parser.y"
        {
            // Simple version - no buffer needed
            (yyval.if_stmt) = new IfStmtNode((yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[0].node));
            register_node((yyval.if_stmt));
        }
#line 2384 "parser.tab.c"
    break;

  case 56: /* iteration_statement: WHILE '(' expression ')' statement  */
#line 512 "parser.y"
        {
            (yyval.while_stmt) = new WhileStmtNode((yyvsp[-2].node), (yyvsp[0].node));
            register_node((yyval.while_stmt));
        }
#line 2393 "parser.tab.c"
    break;

  case 57: /* printf_statement: PRINTF '(' STRING_LITERAL ')' ';'  */
#line 521 "parser.y"
        {
            (yyval.printf_stmt) = new PrintfStmtNode((yyvsp[-2].str));
            register_node((yyval.printf_stmt));
            free((yyvsp[-2].str));
        }
#line 2403 "parser.tab.c"
    break;

  case 58: /* printf_statement: PRINTF '(' STRING_LITERAL ',' argument_list ')' ';'  */
#line 527 "parser.y"
        {
            (yyval.printf_stmt) = new PrintfStmtNode((yyvsp[-4].str));
            (yyval.printf_stmt)->args = *(yyvsp[-2].node_list);
            register_node((yyval.printf_stmt));
            free((yyvsp[-4].str));
            delete (yyvsp[-2].node_list);
        }
#line 2415 "parser.tab.c"
    break;

  case 59: /* return_statement: RETURN expression ';'  */
#line 538 "parser.y"
        {
            (yyval.return_stmt) = new ReturnStmtNode((yyvsp[-1].node), current_function_name);
            register_node((yyval.return_stmt));
        }
#line 2424 "parser.tab.c"
    break;

  case 60: /* return_statement: RETURN ';'  */
#line 543 "parser.y"
        {
            (yyval.return_stmt) = new ReturnStmtNode(nullptr, current_function_name);
            register_node((yyval.return_stmt));
        }
#line 2433 "parser.tab.c"
    break;

  case 61: /* argument_list: expression  */
#line 551 "parser.y"
        {
            (yyval.node_list) = new std::vector<ASTNode*>();
            (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 2442 "parser.tab.c"
    break;

  case 62: /* argument_list: argument_list ',' expression  */
#line 556 "parser.y"
        {
            (yyval.node_list) = (yyvsp[-2].node_list);
            (yyval.node_list)->push_back((yyvsp[0].node));
        }
#line 2451 "parser.tab.c"
    break;

  case 63: /* expression: assignment_expression  */
#line 564 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2459 "parser.tab.c"
    break;

  case 64: /* assignment_expression: logical_or_expression  */
#line 571 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2467 "parser.tab.c"
    break;

  case 65: /* assignment_expression: postfix_expression '=' assignment_expression  */
#line 575 "parser.y"
        {
            // Special case: if right side is a function call, we need to split this
            if (auto* funcCall = dynamic_cast<FunctionCallNode*>((yyvsp[0].node))) {
                // Create a compound statement representing run + use of global var
                auto compound = new CompoundStmtNode();
                
                // Create the run statement
                auto runExpr = new ExprStmtNode((yyvsp[0].node));
                compound->statements.push_back(runExpr);
                
                // Get the appropriate global variable name
                std::string returnVar = funcCall->name + "_result";
                
                // Create assignment from global var to target variable
                auto global = new IdentifierNode(returnVar);
                auto assign = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::ASSIGN, global);
                auto assignStmt = new ExprStmtNode(assign);
                
                compound->statements.push_back(assignStmt);
                
                (yyval.node) = compound;
            } else {
                // Normal assignment
                (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::ASSIGN, (yyvsp[0].node));
            }
            
            register_node((yyval.node));
        }
#line 2500 "parser.tab.c"
    break;

  case 66: /* logical_or_expression: logical_and_expression  */
#line 607 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2508 "parser.tab.c"
    break;

  case 67: /* logical_or_expression: logical_or_expression OR logical_and_expression  */
#line 611 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::OR, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2517 "parser.tab.c"
    break;

  case 68: /* logical_and_expression: equality_expression  */
#line 619 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2525 "parser.tab.c"
    break;

  case 69: /* logical_and_expression: logical_and_expression AND equality_expression  */
#line 623 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::AND, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2534 "parser.tab.c"
    break;

  case 70: /* equality_expression: relational_expression  */
#line 631 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2542 "parser.tab.c"
    break;

  case 71: /* equality_expression: equality_expression EQ relational_expression  */
#line 635 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::EQ, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2551 "parser.tab.c"
    break;

  case 72: /* equality_expression: equality_expression NE relational_expression  */
#line 640 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::NE, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2560 "parser.tab.c"
    break;

  case 73: /* relational_expression: additive_expression  */
#line 648 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2568 "parser.tab.c"
    break;

  case 74: /* relational_expression: relational_expression '<' additive_expression  */
#line 652 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::LT, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2577 "parser.tab.c"
    break;

  case 75: /* relational_expression: relational_expression '>' additive_expression  */
#line 657 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::GT, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2586 "parser.tab.c"
    break;

  case 76: /* relational_expression: relational_expression LE additive_expression  */
#line 662 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::LE, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2595 "parser.tab.c"
    break;

  case 77: /* relational_expression: relational_expression GE additive_expression  */
#line 667 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::GE, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2604 "parser.tab.c"
    break;

  case 78: /* additive_expression: multiplicative_expression  */
#line 675 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2612 "parser.tab.c"
    break;

  case 79: /* additive_expression: additive_expression '+' multiplicative_expression  */
#line 679 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::ADD, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2621 "parser.tab.c"
    break;

  case 80: /* additive_expression: additive_expression '-' multiplicative_expression  */
#line 684 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::SUB, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2630 "parser.tab.c"
    break;

  case 81: /* multiplicative_expression: unary_expression  */
#line 692 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2638 "parser.tab.c"
    break;

  case 82: /* multiplicative_expression: multiplicative_expression '*' unary_expression  */
#line 696 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::MUL, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2647 "parser.tab.c"
    break;

  case 83: /* multiplicative_expression: multiplicative_expression '/' unary_expression  */
#line 701 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::DIV, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2656 "parser.tab.c"
    break;

  case 84: /* multiplicative_expression: multiplicative_expression '%' unary_expression  */
#line 706 "parser.y"
        {
            (yyval.node) = new BinaryExprNode((yyvsp[-2].node), BinaryExprNode::MOD, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2665 "parser.tab.c"
    break;

  case 85: /* unary_expression: postfix_expression  */
#line 714 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);
        }
#line 2673 "parser.tab.c"
    break;

  case 86: /* unary_expression: '-' unary_expression  */
#line 718 "parser.y"
        {
            (yyval.node) = new UnaryExprNode(UnaryExprNode::MINUS, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2682 "parser.tab.c"
    break;

  case 87: /* unary_expression: '!' unary_expression  */
#line 723 "parser.y"
        {
            (yyval.node) = new UnaryExprNode(UnaryExprNode::NOT, (yyvsp[0].node));
            register_node((yyval.node));
        }
#line 2691 "parser.tab.c"
    break;

  case 88: /* postfix_expression: primary_expression  */
#line 732 "parser.y"
        {
            (yyval.node) = (yyvsp[0].node);  // Pass through
        }
#line 2699 "parser.tab.c"
    break;

  case 89: /* postfix_expression: postfix_expression '[' expression ']'  */
#line 736 "parser.y"
        {
            // Create array access node from expression
            (yyval.node) = new ArrayAccessNode((yyvsp[-3].node), (yyvsp[-1].node));
            register_node((yyval.node));
        }
#line 2709 "parser.tab.c"
    break;

  case 90: /* postfix_expression: IDENTIFIER '(' ')'  */
#line 742 "parser.y"
        {
            (yyval.node) = new FunctionCallNode((yyvsp[-2].id));
            register_node((yyval.node));
            free((yyvsp[-2].id));
        }
#line 2719 "parser.tab.c"
    break;

  case 91: /* postfix_expression: IDENTIFIER '(' argument_list ')'  */
#line 748 "parser.y"
        {
            auto call = new FunctionCallNode((yyvsp[-3].id));
            call->args = *(yyvsp[-1].node_list);
            (yyval.node) = call;
            register_node((yyval.node));
            free((yyvsp[-3].id));
            delete (yyvsp[-1].node_list);
        }
#line 2732 "parser.tab.c"
    break;

  case 92: /* primary_expression: IDENTIFIER  */
#line 761 "parser.y"
        {
            (yyval.node) = new IdentifierNode((yyvsp[0].id));
            register_node((yyval.node));
            free((yyvsp[0].id));
        }
#line 2742 "parser.tab.c"
    break;

  case 93: /* primary_expression: NUMBER  */
#line 767 "parser.y"
        {
            (yyval.node) = new NumberNode((yyvsp[0].num));
            register_node((yyval.node));
        }
#line 2751 "parser.tab.c"
    break;

  case 94: /* primary_expression: FLOAT_VAL  */
#line 772 "parser.y"
        {
            (yyval.node) = new FloatNode((yyvsp[0].dval));
            register_node((yyval.node));
        }
#line 2760 "parser.tab.c"
    break;

  case 95: /* primary_expression: CHAR_VAL  */
#line 777 "parser.y"
        {
            (yyval.node) = new CharNode((yyvsp[0].chr));
            register_node((yyval.node));
        }
#line 2769 "parser.tab.c"
    break;

  case 96: /* primary_expression: '(' expression ')'  */
#line 782 "parser.y"
        {
            (yyval.node) = (yyvsp[-1].node);
        }
#line 2777 "parser.tab.c"
    break;


#line 2781 "parser.tab.c"

        default: break;
      }
    if (yychar_backup != yychar)
      YY_LAC_DISCARD ("yychar change");
  }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyssp, yyesa, &yyes, &yyes_capacity, yytoken};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        if (yychar != YYEMPTY)
          YY_LAC_ESTABLISH;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          YYNOMEM;
      }
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  /* If the stack popping above didn't lose the initial context for the
     current lookahead token, the shift below will for sure.  */
  YY_LAC_DISCARD ("error recovery");

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  if (yyes != yyesa)
    YYSTACK_FREE (yyes);
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}

#line 787 "parser.y"


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
