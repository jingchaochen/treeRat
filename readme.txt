DRAT/DRUP proof checker: treeRat
Authors : Jingchao Chen

treeRat can be built with g++ command:
./build.sh

For running
cd bin 
./treeRat <FORMULA> <PROOF>

For outputting TraceCheck+ dependency graphs
./treeRat <FORMULA> <PROOF> -trace -trace-file=<FILE NAME>

A DIMACS CNF <FORMULA> and DRAT/DRUP <PROOF> are mandatory arguments.


