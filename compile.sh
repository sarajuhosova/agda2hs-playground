#!/bin/bash

rm -rf build

# FILES=$(find -name "*.agda" -type f)
# for f in $FILES; do agda2hs $f -o build; done

agda2hs agda/Util.agda -o build
agda2hs agda/Interp/Grammar.agda -o build
agda2hs agda/TypeCheck/TypeChecker.agda -o build
