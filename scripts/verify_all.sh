#!/bin/bash

set -e
set -o pipefail

usage () {
cat <<EOF
Usage: ./scripts/verify_all [-dfs|-bfs|-np|-ltl] [-armv7m|-rv32] [-correction] \
[-plan]

[-dfs|-bfs|-np|-ltl]: Specify a search algorithm for Spin model checker.
[-armv7m|-rv32]: Specify an architecture.
[-correction]: Append this argument to verify corrective applications.
[-plan]: Verify all applications with each of the specified configurations
         in the directory "./scripts/FreeRTOSConfig_plans".
EOF
}

# No specified plan by default
USE_PLANS=_

OPTION=safety_dfs
CORRECTION=
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
            CORRECTION="CORRECTION=1"
            ;;
        -armv7m)
            ARCH="ARCH=ARMV7M"
            ;;
        -rv32)
            ARCH="ARCH=RV32"
            ;;
        -plan)
            USE_PLANS=./scripts/FreeRTOSConfig_plans/*.plan.sh
            ;;
        *|-h|--help)
            usage;
            exit 2
            ;;
    esac
    shift
done

record_options () {
    [ -z $ARCH ] && local LOCAL_ARCH="DEFAULT_ARCH" || local LOCAL_ARCH=$ARCH
cat <<EOF
OPTION      : $OPTION
ARCH        : $LOCAL_ARCH
CORRECTION  : $CORRECTION
EOF
}

if [ -d ./outputs ];
then
    rm -rf ./outputs/*
fi
mkdir -p ./outputs

record_options >./outputs/OPTIONS

verification () {
    local out=$1
    local FreeRTOSConfig="$2"

    make $OPTION $CORRECTION TARGET=$demo $ARCH PLAN="$FreeRTOSConfig" | \
        tee $out

    # Polish the output file
    if [ -x "$(command -v awk)" ];
    then
        awk 'BEGIN {LAST_LINE=""} /^Depth=/ {LAST_LINE=$0; next}
            /^pan: resizing hashtable to/ {print $0; next}
            LAST_LINE!="" {print "Depth= ..."; print LAST_LINE; LAST_LINE=""}
            {print $0}' $out > $out.tmp && mv $out.tmp $out
    fi
}

verify_all_demos () {
    local out_dir=$1
    shift

    local DEMOS=./Demo/*.pml
    for demo in $DEMOS
    do
        local out_file=$out_dir/$(basename -s .pml $demo).result
        verification $out_file "$*"
    done
}

use_plan () {
    local plan=$1

    if [ -f $plan ];
    then
        source $plan
        local out_dir=./outputs/$(basename -s .plan.sh $plan)
        mkdir -p $out_dir
    else
        local out_dir=./outputs
    fi

    verify_all_demos $out_dir $FreeRTOSConfig_PLAN

    unset FreeRTOSConfig_PLAN
}

for plan in $USE_PLANS
do
    use_plan $plan
done
