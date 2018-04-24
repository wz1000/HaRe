#!/bin/bash

# docker run --rm -i -t -v `pwd`:/home/hare hare-8.4.2rc1  /bin/bash
# docker pull alanz/haskell-8.4.2rc1
docker run --rm -i -t -v `pwd`:/home/hare alanz/haskell-8.4.2  /bin/bash
