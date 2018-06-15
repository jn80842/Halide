#!/bin/bash

declare -a varnames=("_0" "_1" "c0" "c1")

for i in "${varnames[@]}"
do
  echo "(declare-const $i Int)"
done

echo ""
echo "(declare-fun max (Int Int) Int)"
echo "(declare-fun min (Int Int) Int)"
echo ""

for i in "${!varnames[@]}"
do 
  for j in "${!varnames[@]}"
  do
    if [ $i -lt $j ] ; then
      echo "(assert (>= (max ${varnames[$i]} ${varnames[$j]}) ${varnames[$i]}))"
      echo "(assert (>= (max ${varnames[$i]} ${varnames[$j]}) ${varnames[$j]}))"
      echo "(assert (or (= ${varnames[$i]} (max ${varnames[$i]} ${varnames[$j]})) (= ${varnames[$j]} (max ${varnames[$i]} ${varnames[$j]}))))"
      echo "(assert (= (max ${varnames[$i]} ${varnames[$j]}) (max ${varnames[$j]} ${varnames[$i]})))" 
      echo ""

      echo "(assert (<= (min ${varnames[$i]} ${varnames[$j]}) ${varnames[$i]}))"
      echo "(assert (<= (min ${varnames[$i]} ${varnames[$j]}) ${varnames[$j]}))"
      echo "(assert (or (= ${varnames[$i]} (min ${varnames[$i]} ${varnames[$j]})) (= ${varnames[$j]} (min ${varnames[$i]} ${varnames[$j]}))))"
      echo "(assert (= (min ${varnames[$i]} ${varnames[$j]}) (min ${varnames[$j]} ${varnames[$i]})))"
      echo ""
    fi
  done
done
