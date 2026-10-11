# Remaining work

No proof obligations remain for Theorem 1.1 or the ordinary and fractional counterexample endpoints. The complete construction compiles and passes Lax kernel replay in the pinned archive environment. All 1,260 annotated proofs are closed, and the freshness-enforcing completion checker reports all three targets CLOSED. The three actual endpoint proofs use only `propext`, `Classical.choice`, and `Quot.sound`. No submission has been made.

The proof route is documented in [PROOF_PLAN.md](PROOF_PLAN.md), and its immutable source pin is in [upstream-construction.json](references/upstream-construction.json).

## Completed checks

- The entire proof package and `AxiomAudit.lean` compile in the archive's pinned Lean environment.
- The transitive axiom audit reports only Lean's three standard background axioms for the construction and both consequences.
- `lax build . --replay` passes with 372 concepts and 1,260 closed annotated proofs; `python3 scripts/check_completion.py` exits with status 0.
- The adapter proves the exact local statement. The touching-matching numbers are definitionally equal (`rfl`), and its proof has no graph-existence or supersaturation assumption.

## Optional future integration

The independently developed local route still has unfinished wrappers and later-section interfaces. Those tasks are preserved in [local-development-checkpoint.md](references/local-development-checkpoint.md) and the historical part of [PROOF_PLAN.md](PROOF_PLAN.md). They may be integrated with the upstream route later, but are not required by the completed endpoint's proof term.

The vendored source contains the complete parameter, supersaturation, graph-transfer, and status/limit arguments. Maintain the immutable pin and provenance when changing it. Publishing to Lax remains a separate action.
