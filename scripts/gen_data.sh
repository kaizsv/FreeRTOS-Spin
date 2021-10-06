#!/bin/bash

set -e
set -o pipefail

if [ ! -d ./outputs ];
then
    echo Please run ./scripts/verify_all.sh to gather the verification results.
    exit 2
fi

CSV_FILE=./outputs/data.csv
rm -f $CSV_FILE

echo "OPTION,$(grep OPTION ./outputs/OPTIONS | cut -d':' -f 2)" >>$CSV_FILE
echo "ARCH,$(grep ARCH ./outputs/OPTIONS | cut -d':' -f 2)" >>$CSV_FILE
echo "CORRECTION,$(grep CORRECTION ./outputs/OPTIONS | cut -d':' -f 2)" >>$CSV_FILE
echo >>$CSV_FILE

dirs_in_output=$(find ./outputs/* -maxdepth 0 -type d)
apps_in_demos=$(find ./Demo/*.pml -maxdepth 0 -type f)

_time () {
    local pan_error=$(grep errors $1 | rev | cut -d' ' -f 1)
    if [ $pan_error == '0' ];
    then
        local pan_search_depth=$(grep 'max search depth too small' $1)
        if [ -z "$pan_search_depth" ];
        then
            local pan_time=$(grep 'elapsed time' $1 | cut -d' ' -f 4)
            echo -n ",$pan_time" >>$CSV_FILE
        else
            echo -n ",$pan_search_depth" >>$CSV_FILE
        fi
    elif [ $pan_error == '1' ];
    then
        echo -n ",error" >>$CSV_FILE
    else
        echo Extend this script to handle skipped errors
        exit 2
    fi
}

_memory () {
    local pan_memory_bound=$(grep 'reached -DMEMLIM bound' $1)
    if [ -z "$pan_memory_bound" ];
    then
        local pan_memory=$(grep 'total actual' $1 | cut -d$'\t' -f 1)
        echo -n ",\"=ROUND($pan_memory/1024,1)\"" >>$CSV_FILE
    else
        echo -n ",Out of memory" >>$CSV_FILE
    fi
}

check () {
    # Table Header
    if [ ! -z "$dirs_in_output" ];
    then
        for dir in $dirs_in_output
        do
            echo -n ",$(basename $dir)" >>$CSV_FILE
        done
        echo >>$CSV_FILE
    fi
    # Table Body
    for app in $apps_in_demos
    do
        # Table Field
        echo -n "$(basename $app)" >>$CSV_FILE

        # Content
        if [ -z "$dirs_in_output" ];
        then
            the_result=./outputs/$(basename -s .pml $app).result
            $1 $the_result
        else
            for dir in $dirs_in_output
            do
                the_result=$dir/$(basename -s .pml $app).result
                $1 $the_result
            done
        fi
        echo >>$CSV_FILE
    done
}

echo -e ",(Verification Time in Seconds)\n" >>$CSV_FILE
check _time

echo -e "\n\n\n,(Total Memory Usage in GB)\n" >>$CSV_FILE
check _memory

exit 0
