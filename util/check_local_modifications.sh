#!/bin/bash

if [[ $(git status -s) ]]; then
    echo "Local modifications found:"
    git status -s
    exit 1
else
    exit 0
fi
