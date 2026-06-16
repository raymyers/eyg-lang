{
  description = "Lean 4 formalization subproject for EYG (depends on cslib + mathlib)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        devShells.default = pkgs.mkShell {
          name = "eyg-lean";

          # `elan` manages the actual Lean toolchain pinned in ./lean-toolchain,
          # so the version stays in sync with cslib/mathlib without being baked
          # into the Nix store. `lake` and `lean` are provided via elan.
          packages = [
            pkgs.elan
            pkgs.git
          ];

          shellHook = ''
            echo "EYG Lean dev shell — toolchain from ./lean-toolchain (managed by elan)"
            echo "First-time setup:"
            echo "  lake update         # resolve cslib + mathlib into lake-manifest.json"
            echo "  lake exe cache get  # download prebuilt mathlib oleans"
            echo "  lake build          # build the Eyg library"
          '';
        };
      });
}
