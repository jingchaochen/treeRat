
#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/stat.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/checker.h"

using namespace treeRat;

BoolOption    forward ("forward mode", "f",    "foreward check", false);

//=================================================================================================

int main(int argc, char** argv)
{
  printf("c\nc This is treeRat, which supports drat formats\nc\n");
    try {
        setUsageHelp("c USAGE: %s <input-file> <RAT-output-file> <OPTIONS>\n\n");
        
        parseOptions(argc, argv, true);
        int ret=0;
        checker S;
        double initial_time = cpuTime();
        
        if (argc < 3){
               printf("c Reading from standard input... Use '--help' for help.\n");
               exit(0);
        }

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        parse_DIMACS(in, S);
        gzclose(in);
        
        printf("c variables #:%12d\n", S.nVars());
        printf("c clauses   #:%12d\n", S.nClauses());
      
        S.readratOutput(argv[2]);
        if( S.ok == false){
                printf("c this proof is verified by a trival check \n");
                return 1;
        }
        else{
           if(forward) ret=S.forwardCheck();
           else ret=S.backwardCheck();
        }
        double check_time = cpuTime();
        printf("c |  check time:  %12.2f s |\n", check_time - initial_time);
        return ret;
    } catch (OutOfMemoryException&){
                printf("c INDETERMINATE\n");
                exit(0);
    }
}

