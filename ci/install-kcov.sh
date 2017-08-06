#!/usr/bin/env bash

# Exit with an error if any command fails
set -e

wget https://github.com/SimonKagstrom/kcov/archive/master.tar.gz
tar xzf master.tar.gz

cd kcov-master
mkdir build

cd build
cmake ..
make
make install DESTDIR=../../kcov-build
