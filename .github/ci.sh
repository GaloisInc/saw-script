#!/usr/bin/env bash
set -Eeuo pipefail

[[ "$RUNNER_OS" == 'Windows' ]] && IS_WIN=true || IS_WIN=false
BIN=bin
EXT=""
$IS_WIN && EXT=".exe"
mkdir -p "$BIN"

is_exe() { [[ -x "$1/$2$EXT" ]] || command -v "$2" > /dev/null 2>&1; }

extract_exe() {
  exe="$(cabal v2-exec which "$1$EXT")"
  name="$(basename "$exe")"
  echo "Copying $name to $2"
  mkdir -p "$2"
  cp -f "$exe" "$2/$name"
  $IS_WIN || chmod +x "$2/$name"
}

setup_dist_bins() {
  is_exe "dist/bin" "saw" && is_exe "dist/bin" "jss" && return
  extract_exe "saw" "dist/bin"
  extract_exe "jss" "dist/bin"
  strip dist/bin/saw*
  strip dist/bin/jss*
}

install_z3() {
  is_exe "$BIN" "z3" && return

  case "$RUNNER_OS" in
    Linux) file="ubuntu-16.04.zip" ;;
    macOS) file="osx-10.14.6.zip" ;;
    Windows) file="win.zip" ;;
  esac
  curl -o z3.zip -sL "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/z3-$Z3_VERSION-x64-$file"

  if $IS_WIN; then 7z x -bd z3.zip; else unzip z3.zip; fi
  cp z3-*/bin/z3$EXT $BIN/z3$EXT
  $IS_WIN || chmod +x $BIN/z3
  rm z3.zip
}

install_cvc4() {
  is_exe "$BIN" "cvc4" && return
  version="${CVC4_VERSION#4.}" # 4.y.z -> y.z

  case "$RUNNER_OS" in
    Linux) file="x86_64-linux-opt" ;;
    Windows) file="win64-opt.exe" ;;
    macOS) file="macos-opt" ;;
  esac
  curl -o cvc4$EXT -sL "https://github.com/CVC4/CVC4/releases/download/$version/cvc4-$version-$file"
  $IS_WIN || chmod +x cvc4$EXT
  mv cvc4$EXT "$BIN/cvc4$EXT"
}

install_yices() {
  is_exe "$BIN" "yices" && return
  ext=".tar.gz"
  case "$RUNNER_OS" in
    Linux) file="pc-linux-gnu-static-gmp.tar.gz" ;;
    macOS) file="apple-darwin18.7.0-static-gmp.tar.gz" ;;
    Windows) file="pc-mingw32-static-gmp.zip" && ext=".zip" ;;
  esac
  curl -o "yices$ext" -sL "https://yices.csl.sri.com/releases/$YICES_VERSION/yices-$YICES_VERSION-x86_64-$file"

  if $IS_WIN; then
    7z x -bd "yices$ext"
    mv "yices-$YICES_VERSION"/bin/*.exe "$BIN"
  else
    tar -xzf "yices$ext"
    pushd "yices-$YICES_VERSION" || exit
    sudo ./install-yices
    popd || exit
  fi
  rm -rf "yices$ext" "yices-$YICES_VERSION"
}

build() {
  ghc_ver="$(ghc --numeric-version)"
  cp cabal.GHC-"$ghc_ver".config cabal.project.freeze
  cabal v2-update
  # Limit jobs on windows due to: https://gitlab.haskell.org/ghc/ghc/issues/17926
  if [[ "$ghc_ver" =~ 8.8.3|8.10.1 && $IS_WIN ]]; then JOBS=1; else JOBS=2; fi
  cabal v2-configure -j$JOBS --minimize-conflict-set
  for _ in {1..3}; do # retry due to flakiness with windows builds
    cabal v2-build "$@" saw jss && break
  done
}

build_abc() {
  arch=X86_64
  case "$RUNNER_OS" in
    Linux) os="Linux" ;;
    macOS) os="OSX" ;;
    Windows)
      os="Windows"
      pushd deps/abcBridge/abc-build
      sed -i 's#ABC_USE_PTHREADS"#ABC_DONT_USE_PTHREADS" /D "_XKEYCHECK_H"#g' -- *.dsp
      awk 'BEGIN { del=0; } /# Begin Group "uap"/ { del=1; } /# End Group/ { if( del > 0 ) {del=0; next;} } del==0 {print;} ' abclib.dsp > tmp.dsp
      cp tmp.dsp abclib.dsp
      rm tmp.dsp
      unix2dos -- *.dsp
      popd
      ;;
  esac
  pushd deps/abcBridge
  scripts/build-abc.sh $arch $os
}

install_system_deps() {
  install_z3 &
  install_cvc4 &
  install_yices &
  wait
  export PATH=$PWD/$BIN:$PATH
  echo "::add-path::$PWD/$BIN"
  is_exe "$BIN" z3 && is_exe "$BIN" cvc4 && is_exe "$BIN" yices
}

test_dist() {
  setup_dist_bins
  pushd intTests
  for t in test0001 test0019_jss_switch_statement test_crucible_jvm test_ecdsa test_examples test_issue108 test_tutorial1 test_tutorial2 test_tutorial_w4; do echo $t >> disabled_tests.txt; done
  RT_JAR=/usr/lib/jvm/java-8-openjdk-amd64/jre/lib/rt.jar LOUD=true ./runtests.sh
}

COMMAND="$1"
shift

"$COMMAND" "$@"
