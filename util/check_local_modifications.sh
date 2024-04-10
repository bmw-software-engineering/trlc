#!/bin/bash

if [[ $(git status -s) ]]; then
    echo "Local modifications found:"
    git -P diff
    echo "Summary:"
    git status -s
    exit 0
else
    exit 0
fi
