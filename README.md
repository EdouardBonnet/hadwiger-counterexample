# Hadwiger counterexample

Lean formalization of OpenAI's [A counterexample to Hadwiger's conjecture](references/openai/hadwiger-counterexample.pdf), dated September 23, 2026.

**Status: complete and locally kernel-replayed. Not submitted.**
The Lax identifier is `lax-342547`, using Lean `v4.33.0` and the archive's pinned mathlib revision.

## The complete proof

[Construction.lean](proofs/Lax342547Proofs/Construction.lean) proves that, for every lower bound, there are `m` at least that bound and a graph `G : SimpleGraph (Fin m)` satisfying

```lean
G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m
```

It uses the complete binary-frame construction in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, vendored under [Upstream/OAI](proofs/Lax342547Proofs/Upstream/OAI). All 288 upstream OAI modules in the construction's import closure are included as Lean source. The archive and upstream touching-matching numbers are definitionally equal, proved by `rfl`; the adapter converts the strict rational inequality into the integral inequality above.

The [ordinary consequence](proofs/Lax342547Proofs/Counterexample.lean) and [fractional consequence](proofs/Lax342547Proofs/FractionalCounterexample.lean) call this construction proof directly. For `m ≥ 5`, the matching-minor bound and fractional-coloring bounds give

```text
h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G).
```

A connected matching means that its distinct matching edges are pairwise touching. Clique minors use disjoint connected branch sets. The sampled graph is defined on positions, so repeated raw vertices are handled by the construction.

## Validation

Run from the repository root:

```sh
lax build . --replay
python3 scripts/check_completion.py
```

For the explicit transitive axiom audit, run from `proofs/`:

```sh
lake build Lax342547Proofs Lax342547Proofs.AxiomAudit
```

`lax build . --replay` passes with 372 concepts and 1,260 closed annotated proofs. Kernel replay took 19 minutes 19 seconds. `scripts/check_completion.py` exits successfully with all three targets closed. The transitive axiom audit confirms that all three target proof terms use only `propext`, `Classical.choice`, and `Quot.sound`. The completion checker rejects missing replay and stale build output. The vendored construction has no `sorry`, `admit`, implementation axioms, or `native_decide`. The archive reports 208 unused-helper warnings from the retained local and upstream developments.

## Provenance and development history

The original paper, TeX source, and earlier matching-minor proofs remain pinned to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. [source.json](references/source.json) records the paper's SHA-256. The later complete construction has a separate immutable pin and per-file source hashes in [upstream-construction.json](references/upstream-construction.json). All reused source is Apache-2.0 licensed.

The complete construction was available in a newer upstream revision than the project's original source checkout. Its port keeps the archive environment and changes namespaces, imports, and a few mathlib lemma names and simplification steps. The compatibility patch is recorded alongside its provenance.

The independently developed local route is retained, including its checked entropy, frame, moment, realization, phase, and affine-slice results. Its previous progress notes are preserved in [local-development-checkpoint.md](references/local-development-checkpoint.md). [PROOF_PLAN.md](PROOF_PLAN.md) records the completed route and preserves the historical detailed plan; [REMAINING.md](REMAINING.md) records the remaining validation or optional integration work. Open tasks in the historical local route are not assumptions of the complete proof.
