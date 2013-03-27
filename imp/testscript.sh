#!/bin/bash

# Compilet alles en voer uit op test. Geef testnummer als argument op.

./ag-script.sh
cabal install
impc < test/t$1 > test/t$1.new.ssm
