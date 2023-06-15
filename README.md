# michelson-interpreter-python

This repository contains an interpreter for the smart contract language of Tezos blockchain, Michelson.

## Information

The interpreter works step-by-step, meaning that it shows every instruction as a step and gives information about the change of the stack with the instructions. Parsing of Michelson scripts is done by [berkaycagir/michelson-parser](https://github.com/berkaycagir/michelson-parser) and [berkaycagir/michelson-parser-wrapper](https://github.com/berkaycagir/michelson-parser-wrapper), and no dependencies to any external libraries by Tezos exist.

## Usage

Flags and parameters may change from branch to branch but in general you can get help with the `--help` flag:

```text
$ python michelson-interpreter.py --help
Usage: michelson-interpreter.py [OPTIONS] SCRIPT

Options:
  -p, --parameter TEXT  Parameter value for the script  [required]
  -s, --storage TEXT    Storage value for the script  [required]
  --account TEXT        Account as a string
  --address TEXT        Address as a string
  --amount INTEGER      Amount as an int  [default: 0]
  --entrypoint TEXT     Entrypoint as a string  [default: default]
  --gas_limit INTEGER   Gas limit as an int  [default: 0]
  --id INTEGER          id as an int  [default: 0]
  --timestamp INTEGER   Timestamp, an int as an Unix time  [default: 0]
  --help                Show this message and exit.
```

## Branches

This repository contains multiple branches with differing functionalities:

### main

`main` is the initial branch of `michelson-interpreter-python` and contains a barebones step-by-step Michelson interpreter.

### concolic

`concolic` is the initial branch that implements concolic execution for Michelson, and is not complete. This branch was planned to be the main concolic execution branch of this interpreter but as of now it is incomplete and you normally shouldn't need to use this.

### concolic-pct

`concolic-pct` is the actual up-to-date branch that implements concolic execution for Michelson. It uses Z3 as a SMT solver. If in doubt, use this branch.

### concolic-pysmt

`concolic-pysmt` branch is a migration and generalization attempt from the Z3's own Python API to [pysmt/pysmt](https://github.com/pysmt/pysmt), which is a common API for Python that can work with different SMT solvers. This attempt was abandoned due to pySMT only supporting theory of strings for [CVC4](https://github.com/CVC4/CVC4-archived) ([issue](https://github.com/pysmt/pysmt/issues/245), [PR of Z3 support](https://github.com/pysmt/pysmt/pull/260)), which was obsoleted by [CVC5](https://github.com/cvc5/cvc5) at the time of the implementation of this interpreter.
