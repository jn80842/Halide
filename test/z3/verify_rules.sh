#!/bin/bash

regex='\(assert \(not (.*)\)\)'
unsatregex='unsat'

for filename in ../../bin/build/tmp/*.smt2; do
  echo "---------------------------------------------------------------"
  ASSERTION=`cat ${filename}`
  [[ $ASSERTION =~ $regex ]]
  RELATION=${BASH_REMATCH[1]}
  OUTPUT=`cat harness1.smt2 ${filename} harness2.smt2 | z3 -smt2 -in`
  if [[ $OUTPUT =~ $unsatregex ]] 
  then
    echo "The relation $RELATION was verified."
  else
    echo "The relation $RELATION could not be verified."
    echo $OUTPUT
  fi
done
echo "----------------------------------------------------------------"
