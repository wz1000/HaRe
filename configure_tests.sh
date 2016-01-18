#!/bin/sh

# This script is temporary until ghc-mod is fixed to reconfigure on change

# Make sure the tests run against the newly installed environment
(cd test/testdata && cabal clean && cabal configure)

(cd test/testdata/cabal/cabal1 && cabal clean && cabal configure)
(cd test/testdata/cabal/cabal2 && cabal clean && cabal configure)
(cd test/testdata/cabal/cabal3 && cabal clean && cabal configure)
(cd test/testdata/cabal/cabal4 && cabal clean && cabal configure)
(cd test/testdata/cabal/foo    && cabal clean && cabal configure)
