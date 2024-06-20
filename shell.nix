{ 
	nixpkgs ? fetchTarball "https://github.com/NixOS/nixpkgs/tarball/e381a1288138aceda0ac63db32c7be545b446921",
}:
let pkgs = import nixpkgs {}; in
pkgs.mkShell {
	buildInputs = with pkgs; [
		# Package goes there
		# You can search packages via `nix search $term` or from https://search.nixos.org/packages
		(agda.withPackages (packages: [ 
			packages.standard-library 
		]))
	];
}
