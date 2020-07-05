%{
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constant.h"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/ToolOutputFile.h"

#include <memory>
#include <algorithm>
#include <list>
#include <vector>
#include <utility>
#include <stack>

#include "list.h"
#include "symbol.h"
  
using namespace llvm;
using namespace std;

using parameter = pair<Type*,const char*>;
using parameter_list = std::list<parameter>;

vector<BasicBlock*> caselist_blocks;
vector<Constant*> caselist_num;
vector<bool> caselist_breaks;

stack<loop_info> loop_stack;
 
int num_errors;

extern int yylex();   /* lexical analyzer generated from lex.l */

int yyerror(const char *error);
int parser_error(const char*);

void cmm_abort();
char *get_filename();
int get_lineno();

int loops_found=0;

extern Module *M;
extern LLVMContext TheContext;
 
Function *Fun;
IRBuilder<> *Builder;

Value* BuildFunction(Type* RetType, const char *name, 
			   parameter_list *params);

%}

/* Data structure for tree nodes*/

%union {
  bool ibool;
  int inum;
  char * id;
  Type*  type;
  Value* value;
  parameter_list *plist;
  vector<Value*> *arglist;
  BasicBlock *bb;
  Constant* constant;
}

/* these tokens are simply their corresponding int values, more terminals*/

%token SEMICOLON COMMA MYEOF
%token LBRACE RBRACE LPAREN RPAREN LBRACKET RBRACKET

%token ASSIGN PLUS MINUS STAR DIV MOD 
%token LT GT LTE GTE EQ NEQ
%token BITWISE_OR BITWISE_XOR LSHIFT RSHIFT BITWISE_INVERT
%token DOT AMPERSAND 

%token FOR WHILE IF ELSE DO RETURN SWITCH
%token BREAK CONTINUE CASE DEFAULT COLON
%token INT VOID BOOL
%token I2P P2I SEXT ZEXT

/* NUMBER and ID have values associated with them returned from lex*/

%token <inum> CONSTANT_INTEGER /*data type of NUMBER is num union*/
%token <id>  ID

%left EQ NEQ LT GT LTE GTE
%left BITWISE_OR
%left BITWISE_XOR
%left AMPERSAND
%left LSHIFT RSHIFT
%left PLUS MINUS
%left MOD DIV STAR 
%nonassoc ELSE

%type <type> type_specifier

%type <constant> opt_initializer
%type <value> expression bool_expression assign_expression expr_opt
%type <value> lvalue_location primary_expression unary_expression
%type <constant> constant_expression unary_constant_expression
%type <arglist> argument_list argument_list_opt
%type <plist> param_list param_list_opt
%type <inum> constant
%type <ibool> break_stmt break_opt
%%

translation_unit:	  external_declaration
			| translation_unit external_declaration
                        | translation_unit MYEOF
{
  YYACCEPT;
}
;

external_declaration:	  function_definition
                        | global_declaration 
;

function_definition:	  type_specifier ID LPAREN param_list_opt RPAREN
// NO MODIFICATION NEEDED
{
  symbol_push_scope();
  BuildFunction($1,$2,$4);
}
compound_stmt 
{
  symbol_pop_scope();
}

// NO MODIFICATION NEEDED
| type_specifier STAR ID LPAREN param_list_opt RPAREN
{
  symbol_push_scope();
  BuildFunction(PointerType::get($1,0),$3,$5);
}
compound_stmt
{
  symbol_pop_scope();
}
;

global_declaration:    type_specifier STAR ID opt_initializer SEMICOLON
{
   if(is_global_scope())
   {
     Value *gl = new GlobalVariable(*M,PointerType::get($1,0),0,GlobalValue::ExternalLinkage,$4,$3);
     symbol_insert($3,gl);
   }
}
| type_specifier ID opt_initializer SEMICOLON
{
  if(is_global_scope())
   {
     Value *gl = new GlobalVariable(*M,$1,0,GlobalValue::ExternalLinkage,$3,$2);
    symbol_insert($2,gl);
   }
}
;

// YOU MUST FIXME: hacked to prevent segfault on initial testing
opt_initializer:   ASSIGN constant_expression 
{ 
  $$ = $2; 
} 
| 
{ 
  $$ = nullptr; 
} 
;

// NO MODIFICATION NEEDED
type_specifier:		  INT
{
  $$ = Type::getInt64Ty(TheContext);
}
                     |    VOID
{
  $$ = Type::getVoidTy(TheContext);
}
;


param_list_opt:           
{
  $$ = nullptr;
}
| param_list
{
  $$ = $1;
}
;

// USED FOR FUNCTION DEFINITION; NO MODIFICATION NEEDED
param_list:	
param_list COMMA type_specifier ID
{
  $$ = $1;
  $$->push_back( parameter($3,$4) );
}
| param_list COMMA type_specifier STAR ID
{
  $$ = $1;
  $$->push_back( parameter(PointerType::get($3,0),$5));
}
| type_specifier ID
{
  $$ = new parameter_list;
  $$->push_back( parameter($1,$2) );
}
| type_specifier STAR ID
{
  $$ = new parameter_list;
  $$->push_back( parameter(PointerType::get($1,0),$3) );
}
;


statement:		  expr_stmt            
			| compound_stmt        
			| selection_stmt       
			| iteration_stmt    
			| return_stmt      
                        | continue_stmt
                        | default_stmt
;

expr_stmt:	           SEMICOLON            
			|  assign_expression SEMICOLON       
;

local_declaration:    type_specifier STAR ID opt_initializer SEMICOLON
{
  Value * ai = Builder->CreateAlloca(PointerType::get($1,0),0,$3);
  if (nullptr != $4)
    Builder->CreateStore($4,ai);
  symbol_insert($3,ai);
}
| type_specifier ID opt_initializer SEMICOLON
{
  Value * ai = Builder->CreateAlloca($1,0,$2);
  if (nullptr != $3)
    Builder->CreateStore($3,ai);
  symbol_insert($2,ai);  
}
;

local_declaration_list:	   local_declaration
                         | local_declaration_list local_declaration  
;

local_declaration_list_opt:	
			| local_declaration_list
;

compound_stmt:		  LBRACE {
  // PUSH SCOPE TO RECORD VARIABLES WITHIN COMPOUND STATEMENT
  symbol_push_scope();
}
local_declaration_list_opt
statement_list_opt 
{
  // POP SCOPE TO REMOVE VARIABLES NO LONGER ACCESSIBLE
  symbol_pop_scope();
}
RBRACE
;


statement_list_opt:	
			| statement_list
;

statement_list:		statement
		      | statement_list statement
;

break_stmt:               BREAK SEMICOLON
{

}

;

break_opt:
{
  $$ = false;
}
|   break_stmt
{
  $$ = true;
}
;

case_stmt:                CASE constant_expression COLON
{
  BasicBlock *case_block = BasicBlock::Create(TheContext,"CASE.block",Fun);
  caselist_blocks.push_back(case_block);
  caselist_num.push_back($2);
  Builder->SetInsertPoint(case_block);
}
statement_list_opt break_opt
{
  caselist_breaks.push_back($6);
}
;

continue_stmt:            CONTINUE SEMICOLON
{

}
;

default_stmt:             DEFAULT constant_expression COLON
{
  
}
;

case_list: case_stmt
          | case_list case_stmt
;

selection_stmt:		  
IF LPAREN bool_expression RPAREN
{
  BasicBlock *then = BasicBlock::Create(TheContext,"if.then",Fun);
  BasicBlock *elsex = BasicBlock::Create(TheContext,"if.else",Fun);
  BasicBlock *join = BasicBlock::Create(TheContext,"if.join",Fun);
  Value *icmp = $3;
  Builder->CreateCondBr(icmp,then,elsex);
  Builder->SetInsertPoint(then);
  push_loop(then,elsex,join,join);
}
statement 
{
  Builder->CreateBr(get_loop().exit);
  Builder->SetInsertPoint(get_loop().body);
}
ELSE statement
{
  Builder->CreateBr(get_loop().exit);
  Builder->SetInsertPoint(get_loop().exit);
  pop_loop();
}
| SWITCH LPAREN expression RPAREN 
{
  BasicBlock* current_blk = Builder->GetInsertBlock();
  //BasicBlock *defualt_ins = BasicBlock::Create(TheContext,"s.default",Fun);
  BasicBlock *exit = BasicBlock::Create(TheContext,"s.exit",Fun);
  push_loop(current_blk,current_blk,exit,exit);
} 
LBRACE case_list
{
  Builder->SetInsertPoint(get_loop().body);
  SwitchInst* switch_blk = Builder->CreateSwitch($3, get_loop().reinit);
  for(unsigned i=0;i<caselist_num.size();i++)
  {
    switch_blk->addCase((ConstantInt*)caselist_num.at(i), caselist_blocks.at(i));
  }
for(unsigned i=0;i<caselist_num.size();i++)
{
  Builder->SetInsertPoint(caselist_blocks.at(i));
  if(caselist_breaks.at(i))
  {
    Builder->CreateBr(get_loop().exit);
  }
  else
  {
    if(i+1 == caselist_blocks.size())
    {
      Builder->CreateBr(get_loop().exit);
    }
    else
    {
      Builder->CreateBr(caselist_blocks.at(i+1));
    }
  }
}

}
RBRACE
{
  Builder->SetInsertPoint(get_loop().exit);
}
;


iteration_stmt:
WHILE
{
  BasicBlock *expr = BasicBlock::Create(TheContext,"w.expr",Fun);
  BasicBlock *body = BasicBlock::Create(TheContext,"w.body",Fun);
  BasicBlock *exit = BasicBlock::Create(TheContext,"w.exit",Fun);
  Builder->CreateBr(expr);
  Builder->SetInsertPoint(expr);
  push_loop(expr,body,exit,exit);
} 
LPAREN bool_expression RPAREN
{
  Builder->CreateCondBr($4,get_loop().body,get_loop().exit);
  Builder->SetInsertPoint(get_loop().body);
} 
statement
{
  Builder->CreateBr(get_loop().expr);
  Builder->SetInsertPoint(get_loop().exit);
  pop_loop();
}
| FOR LPAREN expr_opt 
{
  BasicBlock *expr = BasicBlock::Create(TheContext,"for.cond",Fun);
  BasicBlock *body = BasicBlock::Create(TheContext,"for.body",Fun);
  BasicBlock *exit = BasicBlock::Create(TheContext,"for.join",Fun);
  BasicBlock *reinit = BasicBlock::Create(TheContext,"for.incmnt",Fun);
  Builder->CreateBr(expr);
  Builder->SetInsertPoint(expr);
  push_loop(expr, body, reinit, exit);
}
SEMICOLON bool_expression 
{
  Builder->CreateCondBr($6,get_loop().body,get_loop().exit);
  Builder->SetInsertPoint(get_loop().reinit);
}
SEMICOLON expr_opt
{
  Builder->CreateBr(get_loop().expr);
  Builder->SetInsertPoint(get_loop().body);
}
RPAREN statement
{
  Builder->CreateBr(get_loop().reinit);
  Builder->SetInsertPoint(get_loop().exit);
  pop_loop();
}
| DO
{
  BasicBlock *expr = BasicBlock::Create(TheContext,"w.expr",Fun);
  BasicBlock *body = BasicBlock::Create(TheContext,"w.body",Fun);
  BasicBlock *exit = BasicBlock::Create(TheContext,"w.exit",Fun);
  Builder->CreateBr(body);
  Builder->SetInsertPoint(body);
  push_loop(expr,body,exit,exit);
} 
statement
{
  Builder->CreateBr(get_loop().expr);
  Builder->SetInsertPoint(get_loop().expr);
} 
WHILE LPAREN bool_expression RPAREN SEMICOLON
{
  Builder->CreateCondBr($7,get_loop().body,get_loop().exit);
  Builder->SetInsertPoint(get_loop().exit);
}
;

expr_opt:  
{
  $$ = nullptr;
}	
| assign_expression
{
  $$ = $1;
}
;

return_stmt:		  RETURN SEMICOLON
{
  Builder->CreateRetVoid();
}
| RETURN expression SEMICOLON
{
  Builder->CreateRet($2);
}
;

bool_expression: expression
{
  if($1->getType()->isIntegerTy(1))
  {
    $$ = Builder->CreateICmpNE(Builder->getInt1(0), $1);
  }
  else
  {
    $$ = Builder->CreateICmpNE(Builder->getInt64(0), $1);
  }
  $1->print(errs(),true); 
} 
;

assign_expression:
lvalue_location ASSIGN expression
{
  LoadInst* var;
  var = dyn_cast<LoadInst>($1);
  if(var == NULL)
  {
    Builder->CreateStore($3,$1);
  }
  else
  {
    Value* addr;
    addr = var->getPointerOperand();
    Builder->CreateStore($3,addr);
  }
}
| expression
{
  $$ = $1;
}
;

expression:
unary_expression
{
  $$ = $1;
}
| expression BITWISE_OR expression
{
  $$ = Builder->CreateOr($1,$3);
}
| expression BITWISE_XOR expression
{
  $$ = Builder->CreateXor($1,$3);
}
| expression AMPERSAND expression
{
  $$ = Builder->CreateAnd($1,$3);
}
| expression EQ expression
{
  $$ = Builder->CreateICmpEQ($1,$3);
}
| expression NEQ expression
{
  $$ = Builder->CreateICmpNE($1,$3);
}
| expression LT expression
{
  $$ = Builder->CreateICmpSLT($1,$3);
}
| expression GT expression
{
  $$ = Builder->CreateICmpSGT($1,$3);
}
| expression LTE expression
{
  $$ = Builder->CreateICmpSLE($1,$3);
}
| expression GTE expression
{
  $$ = Builder->CreateICmpSGE($1,$3);
}
| expression LSHIFT expression
{
  $$ = Builder->CreateShl($1,$3);
}
| expression RSHIFT expression
{
  $$ = Builder->CreateAShr($1,$3);
}
| expression PLUS expression
{
  $$ = Builder->CreateAdd($1,$3);
}
| expression MINUS expression
{
  $$ = Builder->CreateSub($1,$3);
}
| expression STAR expression
{
  $$ = Builder->CreateMul($1,$3);
}
| expression DIV expression
{
  $$ = Builder->CreateFDiv($1,$3);
}
| expression MOD expression
{
  $$ = Builder->CreateSRem($1,$3);
}
| BOOL LPAREN expression RPAREN
{
  $$ = Builder->CreateICmpNE($3,Builder->getInt64(0));
}
| I2P LPAREN expression RPAREN
{
  $$ = Builder->CreateIntToPtr($3,PointerType::get(Builder->getInt64Ty(),0));
}
| P2I LPAREN expression RPAREN
{
  $$ = Builder->CreatePtrToInt($3,Builder->getInt64Ty());
}
| ZEXT LPAREN expression RPAREN
{
  $$ = Builder->CreateZExt($3,Builder->getInt64Ty());
}
| SEXT LPAREN expression RPAREN
{
  $$ = Builder->CreateSExt($3,Builder->getInt64Ty());
}
| ID LPAREN argument_list_opt RPAREN
{
  Value *fn = M->getFunction($1);
  ArrayRef<Value*> arguments(*$3);
  $$ = Builder->CreateCall(fn,arguments,$1);
}
| LPAREN expression RPAREN
{
  $$ = $2;
}
;


argument_list_opt:
{
  
}
| argument_list
{
  $$ = $1;
}
;

argument_list:
expression
{
  $$ = new vector<Value*>;
  $$->push_back($1);
}
| argument_list COMMA expression
{
  $1->push_back($3);
  $$ = $1;
}
;


unary_expression:         primary_expression
{
  $$ = $1;
}
| AMPERSAND primary_expression
{
  LoadInst* var;
  var = dyn_cast<LoadInst>($2);
  if(var != NULL)
  {
    $$ = var->getPointerOperand();
  }
  else
  {
    YYABORT;
  }
}
| STAR primary_expression
{
  $$ = Builder->CreateLoad($2);
}
| MINUS unary_expression
{
  $$ = Builder->CreateSub(Builder->getInt64(0),$2);
}
| PLUS unary_expression
{
  $$ = $2;
}
| BITWISE_INVERT unary_expression
{
  $$ = Builder->CreateNeg($2);
}
;

primary_expression:
lvalue_location
{
  $$ = Builder->CreateLoad($1);
}
| constant
{
  $$ = Builder->getInt64($1);
}
;

lvalue_location:
ID
{
  $$ = symbol_find($1);
}
| lvalue_location LBRACKET expression RBRACKET
{
  Value *base = Builder->CreateLoad($1);
  $$ = Builder->CreateGEP(base,$3); 
}
| STAR LPAREN expression RPAREN
{
  $$ = Builder->CreateLoad($3);
}
;

constant_expression:
unary_constant_expression
{
  $$ = $1;
}
| constant_expression BITWISE_OR constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS | RHS);
}
| constant_expression BITWISE_XOR constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS ^ RHS);
}
| constant_expression AMPERSAND constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS & RHS);
}
| constant_expression LSHIFT constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS << RHS);
}
| constant_expression RSHIFT constant_expression
{
   APInt LHS = $1->getUniqueInteger();
   APInt RHS = $3->getUniqueInteger();
   $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS.lshr(RHS));
}
| constant_expression PLUS constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS + RHS);
}
| constant_expression MINUS constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS - RHS);
}
| constant_expression STAR constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS * RHS);
}
| constant_expression DIV constant_expression
{
   APInt LHS = $1->getUniqueInteger();
   APInt RHS = $3->getUniqueInteger();
   $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),llvm::APIntOps::RoundingSDiv(LHS, RHS, APInt::Rounding::DOWN));
}
| constant_expression MOD constant_expression
{
  APInt LHS = $1->getUniqueInteger();
  APInt RHS = $3->getUniqueInteger();
  bool isnegLHS = LHS.isNegative();
  bool isnegRHS = RHS.isNegative();
  Constant* div = Constant::getIntegerValue(Type::getInt64Ty(TheContext),llvm::APIntOps::RoundingSDiv(LHS, RHS, APInt::Rounding::TOWARD_ZERO));
  APInt divs = div->getUniqueInteger();
  if((!isnegLHS && !isnegRHS) || (!isnegLHS && isnegRHS))
  {
    $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),LHS-RHS*divs);
  }
  else if((isnegLHS && !isnegRHS) || (isnegLHS && isnegRHS))
  {
    $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),RHS*divs-LHS);
  }
}
| I2P LPAREN constant_expression RPAREN
{
  APInt number = $3->getUniqueInteger();
  $$ = Constant::getIntegerValue(PointerType::get(Builder->getInt64Ty(),0),number);
}
| LPAREN constant_expression RPAREN
{
  $$ = $2;
}
;

unary_constant_expression:
constant
{
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext), APInt(64, $1));
}
| MINUS unary_constant_expression
{
  APInt RHS = $2->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),APInt(64, 0) - RHS);
}
| PLUS unary_constant_expression
{
  APInt RHS = $2->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),RHS);
}
| BITWISE_INVERT unary_constant_expression
{
  APInt RHS = $2->getUniqueInteger();
  $$ = Constant::getIntegerValue(Type::getInt64Ty(TheContext),~RHS);
}
;


constant:	          CONSTANT_INTEGER
{
  $$ = $1;
}
;


%%

Value* BuildFunction(Type* RetType, const char *name, 
			   parameter_list *params)
{
  std::vector<Type*> v;
  std::vector<const char*> vname;

  if (params)
    for(auto ii : *params)
      {
	vname.push_back( ii.second );
	v.push_back( ii.first );      
      }
  
  ArrayRef<Type*> Params(v);

  FunctionType* FunType = FunctionType::get(RetType,Params,false);

  Fun = Function::Create(FunType,GlobalValue::ExternalLinkage,
			 name,M);
  Twine T("entry");
  BasicBlock *BB = BasicBlock::Create(M->getContext(),T,Fun);

  /* Create an Instruction Builder */
  Builder = new IRBuilder<>(M->getContext());
  Builder->SetInsertPoint(BB);

  Function::arg_iterator I = Fun->arg_begin();
  for(int i=0; I!=Fun->arg_end();i++, I++)
    {
      // map args and create allocas!
      AllocaInst *AI = Builder->CreateAlloca(v[i]);
      Builder->CreateStore(&(*I),(Value*)AI);
      symbol_insert(vname[i],(Value*)AI);
    }


  return Fun;
}

extern int verbose;
extern int line_num;
extern char *infile[];
static int   infile_cnt=0;
extern FILE * yyin;
extern int use_stdin;

int parser_error(const char *msg)
{
  if (use_stdin)
    printf("stdin:%d: Error -- %s\n",line_num,msg);
  else
    printf("%s:%d: Error -- %s\n",infile[infile_cnt-1],line_num,msg);
  return 1;
}

int internal_error(const char *msg)
{
  printf("%s:%d Internal Error -- %s\n",infile[infile_cnt-1],line_num,msg);
  return 1;
}

int yywrap() {

  if (use_stdin)
    {
      yyin = stdin;
      return 0;
    }
  
  static FILE * currentFile = NULL;

  if ( (currentFile != 0) ) {
    fclose(yyin);
  }
  
  if(infile[infile_cnt]==NULL)
    return 1;

  currentFile = fopen(infile[infile_cnt],"r");
  if(currentFile!=NULL)
    yyin = currentFile;
  else
    printf("Could not open file: %s",infile[infile_cnt]);

  infile_cnt++;
  
  return (currentFile)?0:1;
}

int yyerror(const char* error)
{
  parser_error("Un-resolved syntax error.");
  return 1;
}

char * get_filename()
{
  return infile[infile_cnt-1];
}

int get_lineno()
{
  return line_num;
}

void cmm_abort()
{
  parser_error("Too many errors to continue.");
  exit(1);
}

