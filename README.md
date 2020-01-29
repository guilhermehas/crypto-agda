# cripto-agda

[![Build Status](https://travis-ci.com/guilhermehas/cripto-agda.svg?branch=master)](https://travis-ci.com/guilhermehas/cripto-agda)
[![built with nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

## Link for download
[PDF in GitHub Pages](https://guilhermehas.github.io/cripto-agda/thesis.pdf)

# Description
Cripto currency made in agda

# Build with nix
This project works with nix channel version 18, so it is necessary to run this command before.
```bash
$ nix-channel --add https://nixos.org/channels/nixos-18.09 nixpkgs
$ nix-channel --update
```

Install nix and run this command:
```bash
$ nix-build
```

To put the necessary files to compile locally, run this command:
```bash
$ nix-shell --command "make install"
```


License
----
MIT
