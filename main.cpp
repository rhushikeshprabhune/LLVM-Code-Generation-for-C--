#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include <memory>
#include <algorithm>
using namespace llvm;

extern FILE *yyin;
extern char *outfile;
extern int num_errors;
extern int use_stdin;
extern int verbose;

extern int yywrap(void);
extern int yyparse(void);

Module *M;

extern char **targv;
extern char **arglim;
extern char *infile[];

extern void Cmdlex();
extern void usage();

LLVMContext TheContext;

int
main (int argc, char ** argv)
{
  arglim = argv+argc;
  targv = argv+1;

  Cmdlex();

  if (outfile==NULL)
    outfile = "out.bc";

  if (!use_stdin && !infile[0])
    {
      fprintf(stderr,"Incomplete command line. Usage:\n");
      usage();
      return 1;
    }

  // LLVM idiom for constructing output file.
  std::unique_ptr<ToolOutputFile> Out;  
  std::string ErrorInfo;
  std::error_code EC;
  Out.reset(new ToolOutputFile(outfile, EC,
  				 sys::fs::F_None));

  M  = new Module("p2",TheContext);

  /* Set up initial value for yyin */
  yywrap();

  /* Parse C-- input file */
  int res = yyparse();

  if (verbose)
    {
      M->print(errs(),nullptr,true);
    }
  
  /* If we encounter no errors, dump the Module */
  if (M && res==0 && num_errors==0)
    {
      // Dump function to bitcode
      WriteBitcodeToFile(*M,Out->os());
      
      // LLVM idiom to save output file
      Out->keep();
    }
  else
    {
      fprintf(stderr,"Too many errors to print Module.\n");
    }

  /* Return an error status if it failed */
  return (num_errors==0)?EXIT_SUCCESS:EXIT_FAILURE;
}
