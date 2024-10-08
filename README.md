# jixia

A static analysis tool for Lean 4.

jixia is a new static analysis tool for Lean 4 with two main purposes in mind: building a Lean-aware IDE and extracting
useful data for machine learning.

This project is part of BICMR@PKU AI for math program.

*jixia* stands for *稷下*, where [稷下学宫](https://en.wikipedia.org/wiki/Jixia_Academy) was historically located.

### Features

- Non-instrusive:  No change need to be made on the target file.  This improves cache utilization, notably on mathlib4.
- Single-file analysis
- Source-level info:  Includes information such as source range for each defined function, their arguments and return
  types, etc.
- Easy to extend:  jixia's plugin-based design makes it easy to extend while keeping all the advantages above.

### Usage

jixia comes with several plugins.
- Import: list of imported modules.
- Declaration: source-level info about each declaration (`def`, `theorem`, `inductive`, etc.).
- Symbol: info about symbols (or _constants_ in Lean 4 terminology) after elaboration, including their types and
  reference graph.
- Elaboration: info about the elaboration process, including tactic info.
- Line: proof state at the beginning of each line, as displayed in VSCode infoview.
- AST: a full dump of parsed commands.

Each plugin can be set to output to a json file or be turned off individually.  For example,
```sh
/path/to/jixia -d Example.decl.json -s Example.sym.json -t Example.tac.json -l Example.lines.json Example.lean
```
will generate the corresponding json files from the declaration, symbol, elaboration, and line plugins.  If a flag is
omitted, the corresponding plugin will not run.

When analyzing a module in a package, You must first build your package with `lake build` (or with `lake exe cache get`
for mathlib-based projects).  You also need to set the environment variables to make imports work, by running jixia as
```sh
lake env /path/to/jixia [other arguments]
```
in your project root, i.e., where lakefile.lean is located.

### Notes

##### Initializers

If your file contains `initialize` commands, you may need to use the `-i` flag to enable the execution of
initializers. In particular, you should include this flag when analyzing mathlib4.

##### Compiler Compatibility

jixia must be built with the *exact* same version of Lean as the file to be analyzed.  jixia is
known to be compatible with Lean v4.11.0.
