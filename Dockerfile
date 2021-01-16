FROM nixpkgs/nix-flakes

ENV proj /proj
WORKDIR ${proj}
ADD . $proj

RUN mkdir -p /etc/nix/ && echo "experimental-features = nix-command flakes" >> /etc/nix/nix.conf
RUN nix build

RUN cp -Lpr result /crypto