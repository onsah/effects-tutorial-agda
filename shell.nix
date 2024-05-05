{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
	buildInputs = with pkgs; [
		# Package goes there
		# You can search packages via `nix search $term` or from https://search.nixos.org/packages
		(agda.withPackages (packages: [ 
			packages.standard-library 
		]))
	];
}
