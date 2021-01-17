# crypto-agda

[![Build Status](https://travis-ci.com/guilhermehas/crypto-agda.svg?branch=master)](https://travis-ci.com/guilhermehas/crypto-agda)
[![built with nix](https://builtwithnix.org/badge.svg)](https://builtwithnix.org)

## Link for download
[PDF in GitHub Pages](https://guilhermehas.github.io/crypto-agda/thesis.pdf)

[Slides in GitHub Pages](https://guilhermehas.github.io/crypto-agda/slides.pdf)

# Description
Cryptocurrency made in agda

# Build with nix
It is possible to build the project with nix flakes without needing to clone the repository with this command:
```bash
nix build github:guilhermehas/crypto-agda
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
