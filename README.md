# dsss18
Lecture material for DeepSpec Summer School 2018

## Directory Structure

lf - Software Foundations 1: Logical Foundations
plf - Software Foundations 2: Programming Language Foundations
vfa - Software Foundations 3: Verified Functional Algorithms
qc - Software Foundations 4: QuickChick: Property-Based Testing in Coq
vc - Software Foundations 5: Verifiable C

dw - DeepWeb web server micro-demo

## Download Instructions

Kami is included as a submodule (referencing a repository in the `mit-plv` organization), which means grabbing it requires one of two methods:

1. Recursive cloning:
```
git clone --recurse-submodules https://github.com/DeepSpec/dsss18
```
2. Initializing and updating after-the-fact:
```
git submodule init
git submodule update
```

Then running `make` as usual inside the `kami` subdirectory should work to build the library and examples.



