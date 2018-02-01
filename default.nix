{ p ? <nixpkgs>
, compiler ? "ghc822"
}:
let
  pkg = import p {};
  abc = pkg.callPackage ({ stdenv }: stdenv.mkDerivation rec {
     name = "abc-${version}";
     version = "20160818";
     src = pkg.fetchFromGitHub {
       owner  = "dmjio";
       repo   = "abc";
       rev    = "944a8aadc147db98b1588e661db6bfa476b199a2";
       sha256 = "054skf5ff0vpsrk0lrm6izrillfbpmwxkqwf8v0gfjryzl68vs0j";
     };
     buildInputs = [ ];
     preBuild = ''
       export buildFlags="CC=$CC CXX=$CXX LD=$CXX ABC_USE_NO_READLINE=1 libabc.a"
     '';
     enableParallelBuilding = true;
     installPhase = ''
       mkdir -p $out/lib
       mv libabc.a $out/lib
       # mv libabc.so $out/lib
     '';
     meta = {
       description = "A tool for sequential logic synthesis and formal verification";
       homepage    = "https://people.eecs.berkeley.edu/~alanmi/abc/abc.htm";
       license     = stdenv.lib.licenses.mit;
       platforms   = stdenv.lib.platforms.unix;
       maintainers = [ stdenv.lib.maintainers.thoughtpolice ];
     };
   }){};
  config = {
    allowUnfree = true;
    packageOverrides = pkgs: with pkgs.haskell.lib; {
      haskell = pkgs.haskell // {
	packages = pkgs.haskell.packages // rec {
	  ${compiler} = pkgs.haskell.packages.${compiler}.override {
	     overrides = self: super: {
	       crucible = self.callCabal2nix "crucible" ./deps/crucible/crucible {};
	       crucible-llvm = self.callCabal2nix "crucible-llvm" ./deps/crucible/crucible-llvm {};
	       crucible-saw = self.callCabal2nix "crucible-saw" ./deps/crucible/crucible-saw {};
	       parameterized-utils = self.callCabal2nix "parameterized-utils" ./deps/parameterized-utils {};
	       aig = self.callCabal2nix "aig" ./deps/aig {};
	       cryptol = self.callCabal2nix "cryptol" ./deps/cryptol {};
	       cryptol-verifier = self.callCabal2nix "cryptol-verifier" ./deps/cryptol-verifier {};
	       jvm-verifier = dontCheck (self.callCabal2nix "jvm-verifier" ./deps/jvm-verifier {});
	       llvm-verifier = self.callCabal2nix "llvm-verifier" ./deps/llvm-verifier {};
	       llvm-pretty-bc-parser = self.callCabal2nix "llvm-pretty-bc-parser" ./deps/llvm-pretty-bc-parser {};
	       llvm-pretty = self.callCabal2nix "llvm-pretty" ./deps/llvm-pretty {};
	       saw-core = self.callCabal2nix "saw-core" ./deps/saw-core {};
	       saw-core-aig = self.callCabal2nix "saw-core-aig" ./deps/saw-core-aig {};
	       saw-core-sbv = self.callCabal2nix "saw-core-sbv" ./deps/saw-core-sbv {};
	       jvm-parser = self.callCabal2nix "jvm-parser" ./deps/jvm-parser {};
	       galois-matlab = self.callCabal2nix "galois-matlab" ./deps/crucible/galois-matlab {};
	       abcBridge = addBuildDepends (self.callCabal2nix "abcBridge" (pkgs.fetchFromGitHub {
		 owner = "dmjio";
		 repo = "abcBridge";
		 sha256 = "0b9dglp9i9jwa5ypsf8jfa4kb1zqmy2w79xxrybz69ajxmq2w56q";
		 rev = "f7f99b557159aaaaa087bd62065fcc5b5fa3b003";
	       }){ inherit abc; }) (with pkgs; [wget curl unzip]);
	    };
	  };
	};
      };
    };
  };
in
  let
    pkgs = import p { inherit config; };
  in
    pkgs.haskell.packages.${compiler}.callPackage ./saw-script.nix {}


