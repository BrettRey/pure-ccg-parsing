# The complexity of recognition for pure Combinatory Categorial Grammar

This note addresses a question posed by Schiffer, Kuhlmann and Satta. The input is a grammar and a sentence. Each grammar permits every unrestricted composition rule through its own degree cap. What happens when that cap can grow with the input? [*Tractable Parsing for CCGs of Bounded Degree*, p. 631](https://aclanthology.org/2022.cl-3.4.pdf#page=39)

When the input specifies the rule inventory by its degree cap, a reduction from 3-SAT shows that recognition is NP-hard and is NP-complete for lexica without empty entries. When every slash-direction pattern is listed explicitly, a reduction from Clique shows W[1]-hardness in the cap. Both reductions also apply with substitution rules enabled.

Read the [draft note](pure-ccg-parsing.pdf) or build it from [LaTeX source](pure-ccg-parsing.tex) with `make` and a full TeX Live installation (XeLaTeX, Biber, and latexmk).

## Verification

- [Shapes.lean](Shapes.lean) checks that every bracketing before the final atomic marker implements the queue operations in sentence order. The written proof covers the final marker, clause checks, and complexity bounds.
- [check_sat.py](check_sat.py) and [check_clique.py](check_clique.py) compare the constructions against brute-force decisions. The chart recognizer tries both primary directions and every bracketing.

Run `make test` with Python 3 and Lean 4.36.0 installed through Elan.

## License

The note and documentation are [CC BY 4.0](LICENSE-CC-BY-4.0). The code and build files are [MIT](LICENSE-MIT). See the [licensing notice](LICENSE) for coverage.
