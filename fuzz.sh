#!/bin/bash

mkdir -p triage
go build -o pfuzz cmd/pfuzz/main.go

total_files=$(find ./testfiles/transfuzzTestFiles/ -name topi.sv | wc -l)
echo Found $total_files files

progress=0

for i in testfiles/transfuzzTestFiles/obj_dir_example_sim_*/topi.sv ; do 
    advancement=$(echo "${progress}/${total_files} * 100" | bc)
    echo "[+] Fuzzing $i (${advancement} %)"
    ./pfuzz -n 1000 -strategy smart -mutate -file $i
    #mv mismatches triage/$(dirname $i)
    rm -r dist/
    progress=$(echo $progress + 1 | bc)
done
