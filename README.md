# Mathlib AI helper tool

This tools intention is to help AI developers to parse the mathlib4 theorems and enable them to test their AIs with an interactive lean testing enviroment.

## Getting started

Run

```sh
git submodule update --init --recursive
python -m venv venv
source venv/bin/activate
```

Install lean and lake as suggested [here:](https://lean-lang.org/lean4/doc/quickstart.html)

## Runnig tests

```sh
make test-unit
make test-e2e
```

## Create an data export of mathlib4

Modify the function `generate_training_data` in src/generate/training_data according to your needs.

Test your modified funciton by running its e2e test:

```sh
python -m pytest tests/e2e/test_create_training_data.py   
```

and check that the output format is as you want it to be.

To start the overall export on all mathlab files, clone mathlib4 github repo:

```sh
git clone git@github.com:leanprover-community/mathlib4.git
```

Then you can run the following script to extract the data for all files:

```sh
python scripts/generate_training_data/raw_training_data.py <Path to the cloned mathlib4 repo, e.g. ~/coding/ai/lean/mathlib4/Mathlib >
```

It will generate an output.json file in the project directory for you with your data.

## Acknowledgement

Much of the code is copied and inspired by [Lean Dojo](https://github.com/lean-dojo/LeanDojo). It was mostly reorganized to serve a bigger audience and be faster to execute.
