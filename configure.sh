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


# cabal clean && cabal configure --enable-tests --with-compiler=ghc-8.2.0.20170507
# cabal install --dependencies-only --enable-tests --with-compiler=ghc-8.2.0.20170507

rm -fr dist*
cabal-1.25 new-configure --enable-tests --with-compiler=ghc-8.2.0.20170507 --allow-newer
# cabal-1.25 new-configure  --with-compiler=ghc-8.2.0.20170507
