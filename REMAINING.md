# Remaining work

The complete construction proves Theorem 1.1, and the ordinary and fractional consequences follow from it. Intermediate results are now used through their concept statements so that the Lax proof network records the actual mathematical dependencies. Run the kernel replay and completion checker below after changing this network. The construction has only the standard background axioms; modular consequence proofs additionally use proved concept statements. The Lax submission is tracked in [control issue #191](https://github.com/lax-archive/lax/issues/191).

The proof route is documented in [PROOF_PLAN.md](PROOF_PLAN.md), and its immutable source pin is in [upstream-construction.json](references/upstream-construction.json).

## Completed checks for the corrected network

- The entire proof package and `AxiomAudit.lean` compile in the archive's pinned Lean environment.
- The construction has only the three standard background axioms, and both consequence proofs have their declared concept dependencies.
- `lax build . --replay --profile` passed, with 21 minutes 16 seconds of kernel replay. `python3 scripts/check_completion.py` confirms recursive closure of all 1,260 statements and proofs, including all three targets.
- The compiled-term audit and Lax inspector agree on all 1,696 statement dependencies. The website's projection retains every dependency; no proof bypasses an annotated concept statement.
- The labels are 366 lemmas, two theorems (the final fractional consequence and the central matching-minor bound), and four definition packages. The concept statements and 1,495 theorem signatures in changed proof files are unchanged.
- The adapter proves the exact local statement. The touching-matching numbers are definitionally equal (`rfl`), and its proof has no graph-existence or supersaturation assumption.

## Optional future integration

The independently developed local route still has unfinished wrappers and later-section interfaces. Those tasks are preserved in [local-development-checkpoint.md](references/local-development-checkpoint.md) and the historical part of [PROOF_PLAN.md](PROOF_PLAN.md). They may be integrated with the upstream route later, but are not required by the completed endpoint's proof term.

The vendored source contains the complete parameter, supersaturation, graph-transfer, and status/limit arguments. Maintain the immutable pin and provenance when changing it. The public source is [EdouardBonnet/hadwiger-counterexample](https://github.com/EdouardBonnet/hadwiger-counterexample); the control issue records the archive's submission status.
