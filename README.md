# Introduction to Algebraic Effects Agda Formalization
Agda formalization of the paper "An Introduction to Algebraic Effects and Handlers Invited tutorial paper"[^1] for my Programming Languages Lab Course.

## Setup
Recommended setup requires [direnv](https://direnv.net/) and [Nix](https://nix.dev/install-nix). With those installed, just execute:
```bash
direnv allow
```
it will install everything necessary.

Then you can launch your editor from the project path and it should be able to use `agda` provided from the nix shell.

## Module Structure
Source code is inside `src/effect` directory:

- `Lang` : Exports every other module related to the language.
- `Playground` : Playground file. Suitable for when you just want a file to write.
- `Type` : Types of the effect language.
- `Context` : Value Context.
- `Term` : Terms of the effect language. Intrisically typed and scoped. Therefore, no preservaton lemma is needed.
- `Renaming` : Renaming lemma for terms of both value and computation types.
- `Substitution` : Substitution lemma for terms of both value and computation types.
- `Reduction` : Reduction rules as defined in the paper. Adapted to intrinsic typing.
- `Progress` : Progress lemma for the `Reduction`.
- `Evaluation` : `eval` function to automatically reduce the term according to `Reduction` rules.

## Author(s)
Onur Sahin <sahinonur2000@hotmail.com>

## Glossary
- effect language : programming language defined in the paper.

[^1]: https://www.sciencedirect.com/science/article/pii/S1571066115000705