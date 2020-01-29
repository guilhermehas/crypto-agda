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
docker build --tag cripto-agda .
```

Create the container
```bash
docker run --name cripto cripto-agda
```

Copy the pdf
```bash
docker cp cripto:/proj/result/thesis.pdf .
```

Copy tex files
```bash
docker cp cripto:/proj/result/tex/* docs
```


License
----
MIT
