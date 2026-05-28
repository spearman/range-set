with import <nixpkgs> {};
mkShell {
  buildInputs = [
    cargo-udeps
    gh
    rustup
    yamllint
  ];
}
