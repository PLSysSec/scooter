#!/usr/bin/env bash
set -e
(
  cd enforcement
  cargo test
  (
    cd example-project
    cargo test
  )
  (
    cd migrate
    cargo test
  )
)
(
  cd policy-lang
  cargo test
)
(
  cd static-checker
  cargo test
)
