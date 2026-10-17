#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lake exe cache get
lake build
