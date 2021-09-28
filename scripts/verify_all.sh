#!/bin/bash

set -e
set -o pipefail

usage () {
cat <<EOF
Usage: ./scripts/verify_all [-dfs|-bfs|-np|-ltl] [-armv7m] [-correction]
[-dfs|-bfs|-np|-ltl]: Specify a search algorithm for Spin model checker.
[-armv7m]: Specify an architecture.
[-correction]: Append this argument to verify corrective applications.
EOF
}

OPTION=safety_dfs
ARCH=
while [ $# -gt 0 ];
do
    case "$1" in
        -dfs)
            OPTION=safety_dfs
            ;;
        -bfs)
            OPTION=safety_bfs
            ;;
        -np|-non-progress)
            OPTION=non-progress
            ;;
        -ltl)
            OPTION=acceptance
            ;;
        -correction)
            OPTION="${OPTION} CORRECTION=1"
            ;;
        -armv7m)
            ARCH="ARCH=ARMV7M"
            ;;
        *|-h|--help)
            usage;
            exit 2
            ;;
    esac
    shift
done

if [ -d ./outputs ];
then
    rm -rf ./outputs/*
else
    mkdir -p outputs
fi

DEMOS=Demo/*.pml
for demo in $DEMOS
do
    OUT_FILE=./outputs/$(basename $demo .pml).result
    make $OPTION TARGET=$demo $ARCH | tee $OUT_FILE

    # Polish the output file
    if [ -x "$(command -v awk)" ];
    then
        awk 'BEGIN {LAST_LINE=""} /^Depth=/ {LAST_LINE=$0; next}
            /^pan: resizing hashtable to/ {print $0; next}
            LAST_LINE!="" {print "Depth= ..."; print LAST_LINE; LAST_LINE=""}
            {print $0}' $OUT_FILE > $OUT_FILE.tmp && mv $OUT_FILE.tmp $OUT_FILE
    fi
done
