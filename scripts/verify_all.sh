#!/bin/bash

set -e
set -o pipefail

DEMOS=Demo/*.pml

if [ -d ./outputs ];
then
    rm -rf ./outputs/*
else
    mkdir -p outputs
fi

for demo in $DEMOS
do
    OUT_FILE=./outputs/$(basename $demo .pml).result
    make safety_dfs TARGET=$demo | tee $OUT_FILE

    # Polish the output file
    if command -V awk &> /dev/null
    then
        awk 'BEGIN {LAST_LINE=""} /^Depth=/ {LAST_LINE=$0; next}
            /^pan: resizing hashtable to/ {print $0; next}
            LAST_LINE!="" {print "Depth= ..."; print LAST_LINE; LAST_LINE=""}
            {print $0}' $OUT_FILE > $OUT_FILE.tmp && mv $OUT_FILE.tmp $OUT_FILE
    fi
done
