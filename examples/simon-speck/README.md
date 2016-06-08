# Simon & Speck (64/128 and 128/128)

To run: `./run.sh`

## Cryptol Specifications

From: https://github.com/GaloisInc/cryptol/tree/master/examples/contrib

## C Implementations

### simon-X-Y.c

From: https://github.com/kmarquet/bloc

License: [GPL v2](https://github.com/kmarquet/bloc/blob/master/LICENSE)

Modifications:

* made Encrypt and Decrypt directly calls KeyExpand

* removed dependencies to external libs

### speck.c

From: https://code.google.com/archive/p/speck-cipher/source/default/source

License: GPL v3 (see source file)

Modifications:

* made encrypt and decrypt directly calls speck_expandkey.

* added 128/128 test vector


## Java Implementations

From: https://github.com/timw/bc-java/tree/feature/simon-speck/core/src/main/java/org/bouncycastle/crypto/engines

License: [MIT](https://github.com/timw/bc-java/blob/feature/simon-speck/LICENSE.html)

Modifications:
 
* Removed Bouncy Castle dependency

* Added static encrypt and decrypt helper methods

* Added a main method with test vectors
 

### SimonEngine.java

TODO [#126](https://github.com/GaloisInc/saw-script/issues/126)


### SpeckEngine.java

TODO [#126](https://github.com/GaloisInc/saw-script/issues/126)


## Issues & Workarounds

* Bitcode parsing error [#122](https://github.com/GaloisInc/saw-script/issues/122)

  Workaround: Downgrade XCode Command Line Tools from 7.3 to 7.2
              (http://stackoverflow.com/questions/36250949/revert-apple-clang-version-for-nvcc)

  - Log in to: https://developer.apple.com/downloads/ 
  
  - Download and install: http://adcdownload.apple.com/Developer_Tools/Command_Line_Tools_OS_X_10.11_for_Xcode_7.2/Command_Line_Tools_OS_X_10.11_for_Xcode_7.2.dmg
  
  - Run the following command to switch to the old version: 
  
    ```sudo xcode-select --switch /Library/Developer/CommandLineTools```

    to restore:
    
    ```sudo xcode-select --switch /Applications/XCode.app```
    
  - Run the following command to quickly check clang version: 
  
    ```clang --version```

* Verifying speck.c decrypt using z3 takes too long (interestingly, verifying encrypt using z3 is fine)

  Workaround: Use abc or yices

* Others are filed in [issues](https://github.com/GaloisInc/saw-script/issues/)
