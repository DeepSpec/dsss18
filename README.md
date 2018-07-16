# dsss18
Lecture material for DeepSpec Summer School 2018

## Instructions to download everything properly

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
