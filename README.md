# Probabilistic Concurrent Outcome Logic (pcOL) in Iris-Lean

Based on the paper from POPL 2026: https://doi.org/10.1145/3776651

See [DESIGN.md](DESIGN.md) for the places where the formalization deliberately departs
from the paper.

The main results and the axioms they depend on (in particular, whether they still use
`sorry`) can be listed with `lake env lean scripts/Axioms.lean`.
