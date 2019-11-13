#!/usr/bin/env bash

nix-build -I nixpkgs=https://github.com/NixOS/nixpkgs-channels/archive/nixos-18.09.tar.gz

# $? stores exit value of the last command
if [ $? -ne 0 ]; then
    echo "nix fail to build"
    exit 1
fi
