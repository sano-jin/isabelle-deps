#!/bin/bash

set -eux

poetry run isabelle-deps $1 > depgraph.mmd
mmdc -i depgraph.mmd -o depgraph.png -s 10
# mmdc -i depgraph.mmd -o depgraph.svg
