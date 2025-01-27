# Formalizing Brunn-Minkowski theory

## Setup

1. Install [Lean 4 + VSCode](https://docs.lean-lang.org/lean4/doc/quickstart.html).
2. Clone this repository.
3. `lake exe cache get`
4. Install `pygraphviz`
   
   This is tricky for MacOS (I don't know how to proceed with Windows).
   For modern MacOS, do the following.
   ```
   brew install graphviz

   export PATH=$(brew --prefix graphviz):$PATH
   export CFLAGS="-I $(brew --prefix graphviz)/include"
   export LDFLAGS="-L $(brew --prefix graphviz)/lib"

   pip install pygraphviz 
   ```
5. `pip install leanblueprint`

## Using Blueprint

We use [Lean Blueprint](https://github.com/PatrickMassot/leanblueprint) to
document proof details and sync it with Lean formalization.

See [here](https://github.com/PatrickMassot/leanblueprint?tab=readme-ov-file#local-compilation) on how to use it.

The main file for documentation is `blueprint/src/content.tex`.

## Troubleshooting

Do the following if you have issues with `lake`.

1. `rm -rf .lake`
2. `lake exe cache get`

This will clean out all `.lake` compiled cache and re-download them.

