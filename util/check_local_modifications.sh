#!/bin/bash

if [[ $(git status -s) ]]; then
    echo "Local modifications found:"
    git diff -P
    echo "Summary:"
    git status -s
    exit 1
else
    exit 0
fi
