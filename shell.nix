{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    nativeInputs = with pkgs; [
      lean4
      elan
    ];
}
