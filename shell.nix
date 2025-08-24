with import <nixpkgs> {};
pkgs.mkShell {
  buildInputs = [
    cargo-udeps
    gh
    rustup
    rust-analyzer
    yamllint
  ];
}
