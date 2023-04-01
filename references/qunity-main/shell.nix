{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/refs/tags/22.05.tar.gz") {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    gnumake
    coq
  ];
}
