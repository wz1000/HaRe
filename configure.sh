#!/bin/sh

# This script is temporary until ghc-mod is fixed to reconfigure on change

# cabal clean && cabal configure  --enable-tests --disable-optimization

# # Make sure the tests run against the newly installed environment
# (cd test/testdata && cabal clean && cabal configure)

# (cd test/testdata/cabal/cabal1 && cabal clean && cabal configure)
# (cd test/testdata/cabal/cabal2 && cabal clean && cabal configure)
# (cd test/testdata/cabal/cabal3 && cabal clean && cabal configure)
# (cd test/testdata/cabal/cabal4 && cabal clean && cabal configure)
# (cd test/testdata/cabal/foo    && cabal clean && cabal configure)

rm .ghc.environment.*
rm cabal.project.local
rm -fr dist*
# cabalm new-configure --with-compiler=ghc-8.0.2 --enable-tests
# cabalm new-configure --with-compiler=ghc-8.0.2 --enable-tests


# cabalm new-configure --with-compiler=/opt/ghc/8.4.0.20180204/bin/ghc --enable-tests
cabalm new-configure --with-compiler=/opt/ghc/8.4.0.20180204/bin/ghc --allow-newer
