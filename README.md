# crypto-agda

[![Build Status](https://travis-ci.com/guilhermehas/crypto-agda.svg?branch=master)](https://travis-ci.com/guilhermehas/crypto-agda)
[![built with nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

## Link for download
[PDF in GitHub Pages](https://guilhermehas.github.io/crypto-agda/thesis.pdf)
[Slides in GitHub Pages](https://guilhermehas.github.io/crypto-agda/slides.pdf)

# Description
Cryptocurrency made in agda

# Build with nix
This project works with nix channel version 18, so it is necessary to run this command before.
```bash
nix-channel --add https://nixos.org/channels/nixos-18.09 nixpkgs
nix-channel --update
```

Install nix and run this command:
```bash
nix-build
```

# Build with docker
Create docker image
```bash
docker build --tag crypto-agda .
```

Create the container
```bash
docker run --name crypto crypto-agda
```

Copy the pdf
```bash
docker cp crypto:/crypto/thesis.pdf .
```

Copy tex files
```bash
docker cp crypto:/crypto/tex .
mv tex/* docs
rm -rf tex
```


License
----
MIT
