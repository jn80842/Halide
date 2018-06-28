#!/bin/bash

regex='\(assert \(not (.*)\)\)'
unsatregex='^unsat'
unknownregex='^unknown'

show_passing='true'
show_failing='true'
show_unknown='true'

while getopts "fpu" flag ; do
  case $flag in
    f) show_passing='false' ; show_unknown='false' ;;
    p) show_failing='false' ; show_unknown='false' ;;
    u) show_passing='false' ; show_failing='false' ;;
  esac
done

for filename in ../../bin/build/tmp/*.smt2; do
  ASSERTION=`cat ${filename}`
  [[ $ASSERTION =~ $regex ]]
  RELATION=${BASH_REMATCH[1]}
  OUTPUT=`time cat ${filename} | z3 -smt2 -in`
  if [[ $OUTPUT =~ $unsatregex ]] 
  then
    if [[ "$show_passing" == 'true' ]] ; then
      echo "---------------------------------------------------------------"
      echo "Filename: $filename"
      echo "The relation $RELATION was verified."
    fi
  elif [[ $OUTPUT =~ $unknownregex ]]
  then
    if [[ "$show_unknown" == 'true' ]] ; then
      echo "---------------------------------------------------------------"
      echo "Filename: $filename"
      echo "The relation $RELATION could not be determined to be satisfied, but no counterexample could be found."
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

