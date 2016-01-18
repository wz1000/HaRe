#!/bin/sh

# This script is temporary until ghc-mod is fixed to reconfigure on change

cabal clean && cabal configure  --enable-tests --disable-optimization

# Make sure the tests run against the newly installed environment
./configure_tests.sh
