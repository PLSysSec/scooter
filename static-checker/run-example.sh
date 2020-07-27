#! /usr/bin/env bash

cargo run --bin gen ./examples/$1/before.txt ./examples/$1/after.txt | z3 -smt2 -in -t:5000
