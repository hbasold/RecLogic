# RecLogic

## Introduction

This project implements a logic with a recursive proof system, which is based
on the so-called later modalitity.
The logic can be used to reason about inductive-coinductive programs that are
implemented in the copattern calculus.
Thus far, the implementation is not yet complete.


## Usage

The proof checker can be build by running cabal configure and then cabal build.
To use it, just run ./dist/build/RecLogic-exe/RecLogic-exe -s [file] in the
current directory.

## Examples

There are some example programs in the example directory.
For instance, in StreamPlusComm.cp, addition on natural numbers and streams over
natural numbers are defined, and it is proven that both are commutative.
In StreamDerivative.cp, an example is shown that is not provable by using the
induction scheme that is induced as a recursive proof.