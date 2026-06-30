{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOs/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        my-lean =  pkgs.callPackage /home/nartan/Documents/phd/patched_lean/default.nix { };
      in rec {
         devShells.default = pkgs.mkShell {
          name = "hammer_time-dev";
          packages = with pkgs; [ my-lean elan ];
       };

    });


}
