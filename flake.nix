{
  inputs = {
    nixpkgs = {
      url = "github:nixos/nixpkgs";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          t    = pkgs.lib.trivial;
          hl   = pkgs.haskell.lib;

          # hpkgs = pkgs.haskell.packages.ghc924;

          cabal-repo = pkgs.fetchFromGitHub {
            owner = "sergv";
            repo = "cabal";
            rev = "dev";
            sha256 = "sha256-m0hHnC460ZoB9o/YweRMCG5onqgMrwPfexYzZDriR30="; # pkgs.lib.fakeSha256;
          };

          hpkgs = pkgs.haskell.packages.ghc942;
          # hpkgs = pkgs.haskell.packages.ghc924;

          hpkgsCabal = pkgs.haskell.packages.ghc924.override {
            overrides = self: super: {
              Cabal = self.callCabal2nix
                "Cabal"
                (cabal-repo + "/Cabal")
                {};
              Cabal-syntax = self.callCabal2nix
                "Cabal-syntax"
                (cabal-repo + "/Cabal-syntax")
                {};
              cabal-install-solver = self.callCabal2nix
                "cabal-install-solver"
                (cabal-repo + "/cabal-install-solver")
                {};
              cabal-install = self.callCabal2nix
                "cabal-install"
                (cabal-repo + "/cabal-install")
                { inherit (self) Cabal-described Cabal-QuickCheck Cabal-tree-diff;
                };
              process = pkgs.haskell.lib.dontCheck
                (self.callHackage "process" "1.6.15.0" {});
            };
          };

          # name = "linux-scripts";

          nativeDeps = [
            # (builtins.trace "stdenv.cc.cc.lib = ${pkgs.stdenv.cc.cc.lib}"
            #   pkgs.stdenv.cc.cc.lib)

            pkgs.gmp
            pkgs.libffi
            pkgs.zlib
          ];

      in {
        devShell = pkgs.mkShell {

          buildInputs = nativeDeps;

          nativeBuildInputs = [
            pkgs.gdb

            hpkgs.ghc
            hpkgsCabal.cabal-install
            pkgs.clang_13
            pkgs.llvm_13
            pkgs.lld_13
            # hpkgs.haskell-language-server
            # hpkgs.hlint
          ] ++ map (x: if builtins.hasAttr "dev" x then x.dev else x) nativeDeps;

          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath nativeDeps;

          # # Add executable packages to the nix-shell environment.
          # packages = [
          #   # hpkgs.ghc
          #   # hpkgs.cabal-install
          #   pkgs.zlib
          # ];

          # Add build dependencies of the listed derivations to the nix-shell environment.
          # inputsFrom = [ pkgs.hello pkgs.gnutar ];

          # ... - everything mkDerivation has
        };
      });
}
