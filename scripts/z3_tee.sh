#! /usr/bin/env sh

tee z3input.txt | z3 -in -smt2 | tee z3output.txt
