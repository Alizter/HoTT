{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    coq-lsp = {
      url = "git+https://www.github.com/ejgallego/coq-lsp?submodules=1";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs = { self, flake-utils, nixpkgs, coq-lsp }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        devPackages = {
          # Extra packages for testing

        };
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
    
        devShell =
          pkgs.mkShell {
            nativeBuildInputs = [ pkgs.opam ];
            buildInputs = (with pkgs;
              [
                # dev tools
                dune_3
                coq_8_16
                coq_8_16.ocamlPackages.findlib
              ]) ++ [ coq-lsp.outputs.packages.${system}.coq-lsp ]
            ++ (builtins.map (s: builtins.getAttr s self.packages.${system})
              (builtins.attrNames devPackages));
          };
      });
}
