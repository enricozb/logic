{
  description = "an introduction to mathematical logic in lean";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  inputs.lean4.url = "github:leanprover/lean4/v4.5.0";

  outputs = { self, nixpkgs, flake-utils, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lean4-pkgs = lean4.packages.${system};
      in {
        devShells.default = pkgs.mkShell {
          packages = [ lean4-pkgs.lean-all lean4-pkgs.vscode ];
        };
      });
}
