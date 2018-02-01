{ mkDerivation, abcBridge, aig, alex, ansi-terminal, ansi-wl-pprint
, array, base, binary, bytestring, containers, crucible
, crucible-llvm, crucible-saw, cryptol, cryptol-verifier, deepseq
, directory, either, executable-path, fgl, filepath, free, gitrev
, GraphSCC, happy, haskeline, IfElse, jvm-parser, jvm-verifier
, lens, llvm-pretty, llvm-pretty-bc-parser, llvm-verifier
, monad-supply, mtl, old-locale, old-time, parameterized-utils
, parsec, pretty, pretty-show, process, QuickCheck, saw-core
, saw-core-aig, saw-core-sbv, sbv, smtLib, split, stdenv
, template-haskell, temporary, terminal-size, text, time
, transformers, transformers-compat, utf8-string, vector
, xdg-basedir
}:
mkDerivation {
  pname = "saw-script";
  version = "0.2";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    abcBridge aig ansi-wl-pprint array base binary bytestring
    containers crucible crucible-llvm crucible-saw cryptol
    cryptol-verifier deepseq directory either executable-path fgl
    filepath free GraphSCC haskeline IfElse jvm-parser jvm-verifier
    lens llvm-pretty llvm-pretty-bc-parser llvm-verifier monad-supply
    mtl old-locale old-time parameterized-utils parsec pretty
    pretty-show process saw-core saw-core-aig saw-core-sbv sbv smtLib
    split template-haskell temporary terminal-size text time
    transformers transformers-compat utf8-string vector xdg-basedir
  ];
  libraryToolDepends = [ alex happy ];
  executableHaskellDepends = [
    ansi-terminal base containers cryptol directory either filepath
    gitrev haskeline QuickCheck saw-core transformers
  ];
  license = stdenv.lib.licenses.bsd3;
}
