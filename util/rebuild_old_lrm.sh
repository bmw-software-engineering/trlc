#!/bin/bash

build_lrm ()
{
    echo "Building for $1"
    rm -rf tmp
    mkdir tmp
    git show $1:language-reference-manual/lrm.rsl > tmp/lrm.rsl
    git show $1:language-reference-manual/lrm.trlc > tmp/lrm.trlc
    ./trlc-lrm-generator.py --lrm_dir tmp --tag --update-index
}

# Versions prior to this used MD, so we don't bother

mkdir -p docs

for tag in $(git tag | grep trlc- | sort); do
    echo -e "trlc-1.0.9\n${tag}" | sort -VC && build_lrm ${tag}
done

echo "Building for TRLC (current)"
./trlc-lrm-generator.py --update-index

rm -rf tmp
