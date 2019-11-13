#!/usr/bin/env bash

# nix-build
echo "Commiting"

# $? stores exit value of the last command
if [ $? -ne 0 ]; then
    echo "nix fail to build"
    exit 1
fi
