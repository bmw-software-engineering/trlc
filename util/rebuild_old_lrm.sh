#!/bin/bash

build_lrm ()
{
    echo "Building for TRLC $1"
    rm -rf tmp
    mkdir tmp
    git show trlc-$1:language-reference-manual/lrm.rsl > tmp/lrm.rsl
    git show trlc-$1:language-reference-manual/lrm.trlc > tmp/lrm.trlc
    ./trlc-lrm-generator.py --lrm_dir tmp --tag
}

# Versions prior to this used MD, so we don't bother

build_lrm 1.0.9
build_lrm 1.0.10
build_lrm 1.0.11
build_lrm 1.0.12
build_lrm 1.0.13
build_lrm 1.1.1
build_lrm 1.1.2
build_lrm 1.1.3
build_lrm 1.1.4

echo "Building for TRLC (current)"
./trlc-lrm-generator.py

rm -rf tmp
