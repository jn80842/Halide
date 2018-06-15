#!/bin/bash

regex='\(assert \(not (.*)\)\)'
unsatregex='unsat'

show_passing='true'
show_failing='true'

while getopts "fp" flag ; do
  case $flag in
    f) show_passing='false' ;;
    p) show_failing='false' ;;
  esac
done

for filename in ../../bin/build/tmp/*.smt2; do
  ASSERTION=`cat ${filename}`
  [[ $ASSERTION =~ $regex ]]
  RELATION=${BASH_REMATCH[1]}
  OUTPUT=`cat harness1.smt2 ${filename} harness2.smt2 | z3 -smt2 -in`
  if [[ $OUTPUT =~ $unsatregex ]] 
  then
    if [[ "$show_passing" == 'true' ]] ; then
      echo "---------------------------------------------------------------"
      echo "Filename: $filename"
      echo "The relation $RELATION was verified."
    fi
  else
    if [[ "$show_failing" == 'true' ]] ; then
      echo "---------------------------------------------------------------"
      echo "Filename: $filename"
      echo "The relation $RELATION could not be verified."
      echo $OUTPUT
    fi
  fi
done
echo "----------------------------------------------------------------"

