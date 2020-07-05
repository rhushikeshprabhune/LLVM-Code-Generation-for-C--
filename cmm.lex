%{
#include <string.h>
#include <unistd.h>
#include <list>
#include <utility>
#include <memory>
#include <algorithm>
#include <errno.h>
#include <search.h>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Type.h"

using namespace llvm;
using namespace std;

using parameter = pair<const char*,Type*>;
using parameter_list = std::list<parameter>;


#include "cmm.y.hpp"

int line_num=1;

void lexical_error(const char *);
%}

%x comment

DIGIT   [0-9]
ID      [a-zA-Z_][a-zA-Z_0-9]*
SPACE   [\t ]*
NEWLINE [\n\r]

%{
  /* additional code here */
%}

%option nounput
%option noinput

%%


{SPACE}                   ;
{NEWLINE}                 ++line_num;

";"                     return SEMICOLON;
":"                     return COLON;
","                     return COMMA;

"{"                     return LBRACE;
"}"                     return RBRACE;
"("                     return LPAREN;
")"                     return RPAREN;
"["                     return LBRACKET;
"]"                     return RBRACKET;
"+"                     return PLUS;
"-"                     return MINUS;
"*"                     return STAR;
"/"                     return DIV;
"%"                     return MOD;
"<="                    return LTE;
">="                    return GTE;
"<"                     return LT;
">"                     return GT;
"=="                    return EQ;
"!="                    return NEQ;
"="                     return ASSIGN;
"."                     return DOT;
"&"                     return AMPERSAND;
"|"                     return BITWISE_OR;
"^"                     return BITWISE_XOR;
"<<"                    return LSHIFT;
">>"                    return RSHIFT;
"~"                     return BITWISE_INVERT;

int               return INT;
void              return VOID;
for               return FOR;
while             return WHILE;
if                return IF;
else              return ELSE;
switch            return SWITCH;
case              return CASE;
do                return DO;
inttoptr          return I2P;
ptrtoint          return P2I;
zext              return ZEXT;
sext              return SEXT;
bool              return BOOL;
return            return RETURN;
break             return BREAK;
continue          return CONTINUE;


{DIGIT}*         { yylval.inum = atoi(yytext); return CONSTANT_INTEGER; }
{ID}              { yylval.id = strdup(yytext); return ID; }


"//END"           { return MYEOF; }
"//"[^\n]*         ;

"/*"                    { BEGIN(comment); }

<comment>[^*\n]*        /* eat anything that's not a '*' */
<comment>"*"+[^*/\n]*   /* eat up '*'s not followed by '/'s */
<comment>{NEWLINE}      ++line_num;
<comment>"*"+"/"        BEGIN(0);

.                       lexical_error("Unmatched character");      

%%

void lexical_error(const char *msg)
{
  printf("C-- lexical error(%d): %s\n", line_num, msg);
  exit(-1);
}
