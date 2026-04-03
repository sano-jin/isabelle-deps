#!/bin/bash

set -eux

poetry install --no-root
poetry run python ../main.py $1 > depgraph.mmd
mmdc -i depgraph.mmd -o depgraph.png -s 10
# mmdc -i depgraph.mmd -o depgraph.svg
