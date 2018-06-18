#!/bin/bash

declare -a varnames=("_0" "_1" "_2" "_3" "c0" "c1" "c2")

for i in "${varnames[@]}"
do
  echo "(declare-const $i Int)"
done
