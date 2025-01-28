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
Usage copied from [here](https://github.com/PatrickMassot/leanblueprint?tab=readme-ov-file#local-compilation):

- `leanblueprint pdf` to build the pdf version (this requires a TeX installation of course).
- `leanblueprint web` to build the web version
- `leanblueprint checkdecls` to check that every Lean declaration name that appear in the blueprint exist in the project. **Make sure** to do the followings beforehand.
  - Include any new `.lean` file to the main `BrunnMinkowski.lean` to make it visible to `lake`.
  - Then do `lake build` to make compiled files.
- `leanblueprint all` to run the previous three commands.
- `leanblueprint serve` to start a local webserver showing your local blueprint. The url you should use in your browser will be displayed.

The main file for documentation is `blueprint/src/content.tex`.
Doing
```latex
\begin{theorem}\label{thm:A}\lean{BrunnMikowski.theorem_A}
Theorem A
\end{theorem}

\begin{theorem}\label{thm:B}\uses{thm:A}\lean{BrunnMinkowski.theorem_B}
Theorem B
\end{theorem}
```
will link dependencies and map each theorem/definition to their corresponding Lean definition.

## Troubleshooting

Do the following if you have issues with `lake`.

1. `rm -rf .lake`
2. `lake exe cache get`

This will clean out all `.lake` compiled cache and re-download them.

