{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOs/nixpkgs/nixpkgs-unstable";
  };

  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in rec {
         devShells.default = pkgs.mkShell {
          name = "hammer_time-dev";
          packages = with pkgs; [ lean4 elan isabelle ];
       };

    });


}
