#!/bin/bash

# Assumes that run_all_experiments.sh has run
for app in harris local_laplacian unsharp bilateral_grid camera_pipe nl_means stencil_chain iir_blur interpolate max_filter; do
    echo $app ...
    echo "ours,baseline" > ${app}_runtime.csv
    echo "ours,baseline" > ${app}_peak_memory.csv
    echo "ours,baseline" > ${app}_halide_compile_time.csv
    echo "ours,baseline" > ${app}_llvm_optimization_time.csv
    echo "ours,baseline" > ${app}_llvm_backend_time.csv
    echo "ours,baseline" > ${app}_proof_failures.csv
    echo "ours,baseline" > ${app}_non_monotonic.csv
    echo "ours,baseline" > ${app}_unrolling_failures.csv
    echo "ours,baseline" > ${app}_code_size.csv
    for ((i=0;i<64;i++)); do
        echo -n .
        A=$(grep BEST ../${app}/results/${i}/benchmark_stdout.txt | cut -d' ' -f5)
        B=$(grep BEST ../${app}/results_baseline/${i}/benchmark_stdout.txt | cut -d' ' -f5)        
        echo "$A,$B" >> ${app}_runtime.csv

        A=$(grep memory ../${app}/results/${i}/memory_stdout.txt | cut -d' ' -f4)
        B=$(grep memory ../${app}/results_baseline/${i}/memory_stdout.txt | cut -d' ' -f4)        
        echo "$A,$B" >> ${app}_peak_memory.csv

        A=$(grep Lower.cpp ../${app}/results/${i}/stderr.txt | cut -d' ' -f5)
        B=$(grep Lower.cpp ../${app}/results_baseline/${i}/stderr.txt | cut -d' ' -f5)        
        echo "$A,$B" >> ${app}_halide_compile_time.csv

        A=$(grep CodeGen_LLVM.cpp ../${app}/results/${i}/stderr.txt | cut -d' ' -f5)
        B=$(grep CodeGen_LLVM.cpp ../${app}/results_baseline/${i}/stderr.txt | cut -d' ' -f5)        
        echo "$A,$B" >> ${app}_llvm_optimization_time.csv

        A=$(grep LLVM_Output.cpp ../${app}/results/${i}/stderr.txt | cut -d' ' -f5 | head -n1)
        B=$(grep LLVM_Output.cpp ../${app}/results_baseline/${i}/stderr.txt | cut -d' ' -f5 | head -n1)        
        echo "$A,$B" >> ${app}_llvm_backend_time.csv

        A=$(grep 'Failed to prove' ../${app}/results/${i}/stderr.txt | wc -l)
        B=$(grep 'Failed to prove' ../${app}/results_baseline/${i}/stderr.txt | wc -l)        
        echo "$A,$B" >> ${app}_proof_failures.csv

        # Local laplacian triggers a known bug in the autoscheduler to do with scalar params being treated as constant
        A=$(grep 'Warning: not unrolling' ../${app}/results/${i}/stderr.txt | grep -v 'levels' | wc -l)
        B=$(grep 'Warning: not unrolling' ../${app}/results_baseline/${i}/stderr.txt | grep -v 'levels' | wc -l)        
        echo "$A,$B" >> ${app}_unrolling_failures.csv

        A=$(grep 'non-monotonic' ../${app}/results/${i}/stderr.txt | wc -l)
        B=$(grep 'non-monotonic' ../${app}/results_baseline/${i}/stderr.txt | wc -l)        
        echo "$A,$B" >> ${app}_non_monotonic.csv

        A=$(ls -l ../${app}/results/${i}/${app}.a | cut -d' ' -f5)
        B=$(ls -l ../${app}/results_baseline/${i}/${app}.a | cut -d' ' -f5)        
        echo "$A,$B" >> ${app}_code_size.csv
        
    done
    echo
done

echo harris,,local_laplacian,,unsharp,,bilateral_grid,,camera_pipe,,nl_means,,stencil_chain,,iir_blur,,interpolate,,max_filter, > header.csv

cp header.csv results.csv

for sheet in runtime peak_memory halide_compile_time llvm_optimization_time llvm_backend_time proof_failures unrolling_failures non_monotonic code_size; do
    cp header.csv results_${sheet}.csv
    paste -d, harris_${sheet}.csv local_laplacian_${sheet}.csv unsharp_${sheet}.csv bilateral_grid_${sheet}.csv camera_pipe_${sheet}.csv nl_means_${sheet}.csv stencil_chain_${sheet}.csv iir_blur_${sheet}.csv interpolate_${sheet}.csv max_filter_${sheet}.csv >> results_${sheet}.csv
done

