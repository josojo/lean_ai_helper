# Mathlib AI helper tool

This tools intention is to help AI developers to parse the mathlib4 theorems and enable them to test their AIs with an interactive lean testing enviroment.

## Getting started

Run

```sh
git submodule update --init --recursive
python -m venv venv
source venv/bin/activate
```

## Runnig tests

```sh
make test-unit
make test-e2e
```

## Acknowledgement

Much of the code is copied and inspired by [Lean Dojo](https://github.com/lean-dojo/LeanDojo). It was mostly reorganized to serve a bigger audience and be faster to execute.
