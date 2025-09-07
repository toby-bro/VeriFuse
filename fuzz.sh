#!/bin/bash

go build -o pfuzz cmd/pfuzz/main.go
make build

#path2testfiles=$(pwd -P)/../chimera/3k_programs_for_bugs/transfuzz
path2testfiles="$(pwd -P)/../instrumentedVerilator/valid*"

total_files=$(find ${path2testfiles} -name *.sv | wc -l)
echo Found $total_files files

progress=0

for j in {0..10} ; do
for i in ${path2testfiles}/*.sv ; do 
    advancement=$(echo "${progress}*100/${total_files}" | bc)
    echo "[+] Fuzzing $i (${advancement} %)"
    ./pfuzz mutate -n 1000 -strategy smart -file $i -max-attempts 1
    #mv mismatches triage/$(dirname $i)
    rm -r dist/
    progress=$(echo $progress + 1 | bc)
done
done
