#!/bin/bash

echo harris,,local_laplacian,,unsharp,,bilateral_grid,,camera_pipe,,nl_means,,stencil_chain,,iir_blur,,interpolate,,max_filter > header.csv

while read p; do
  echo "$p"
  arr=()
  for app in harris local_laplacian unsharp bilateral_grid camera_pipe nl_means stencil_chain iir_blur interpolate max_filter; do
    echo "$app"
    total_count=0
    total_baseline_count=0
    for ((i=0;i<4;i++)); do
      count=`grep "matched ${p}" ../${app}/results/${i}/stderr.txt | wc -l | awk '{print $1}'`
      total_count=$(($total_count + $count))
      baseline_count=`grep "matched ${p}" ../${app}/results_baseline/${i}/stderr.txt | wc -l | awk '{print $1}'`
      total_baseline_count=$(($total_baseline_count + $baseline_count))
    done
    echo "${total_count}"
    echo "${total_baseline_count}"
    arr[${#arr[@]}]=${total_count}
    arr[${#arr[@]}]=${total_baseline_count}
  done
  #echo "$(printf ",%d" "${arr[@]}")"
  results=$(printf ",%s" "${arr[@]}")
  echo ${p}${results} >> matched_rules.csv
done <all_rewrite_rules_by_name.txt