#!/bin/bash

set -exo pipefail

git submodule update --init
mkdir -p build
cd build
../tools/cobble/cobble init ..
