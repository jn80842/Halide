#!/bin/bash

declare -a varnames=("_0" "_1" "_2" "_3" "_4" "_5" "c0" "c1" "c2")

for i in "${varnames[@]}"
do
  echo "(declare-const $i Int)"
done

declare -a boolvarnames=("b0" "b1" "b2" "b3")

for i in "${boolvarnames[@]}"
do
  echo "(declare-const $i Bool)"
done

echo "(declare-const lanes Int)"
echo "(assert (<= 0 lanes))"
