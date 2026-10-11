# Hadwiger counterexample

Lean formalization of OpenAI's [A counterexample to Hadwiger's conjecture](references/openai/hadwiger-counterexample.pdf), dated September 23, 2026.

**Status: complete and locally kernel-replayed.** The Lax submission is tracked in
[control issue #191](https://github.com/lax-archive/lax/issues/191).
The Lax identifier is `lax-342547`, using Lean `v4.33.0` and the archive's pinned mathlib revision.

## The complete proof

[Construction.lean](proofs/Lax342547Proofs/Construction.lean) proves that, for every lower bound, there are `m` at least that bound and a graph `G : SimpleGraph (Fin m)` satisfying

```lean
G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m
```

It uses the complete binary-frame construction in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, vendored under [Upstream/OAI](proofs/Lax342547Proofs/Upstream/OAI). All 288 upstream OAI modules in the construction's import closure are included as Lean source. The archive and upstream touching-matching numbers are definitionally equal, proved by `rfl`; the adapter converts the strict rational inequality into the integral inequality above.

The [ordinary consequence](proofs/Lax342547Proofs/Counterexample.lean) and [fractional consequence](proofs/Lax342547Proofs/FractionalCounterexample.lean) use the construction's concept statement. For `m ≥ 5`, the matching-minor bound and fractional-coloring bounds give

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

The submission contains 372 concepts and 1,260 annotated proofs. Proofs import and use concept statements for intermediate results; Lax computes those statement dependencies from their kernel axiom sets. The completion checker verifies recursive closure of the proof network, including every intermediate statement, and rejects missing replay or stale build output. The construction itself uses only `propext`, `Classical.choice`, and `Quot.sound`; the consequence proofs additionally use concept statements that are discharged elsewhere in the network. The vendored construction has no `sorry`, `admit`, implementation axioms, or `native_decide`.

The final fractional counterexample and the central matching-minor bound are labelled `theorem`. Other statement packages are labelled `lemma`; the four packages containing only definitions retain `definition`.

The corrected network passed local kernel replay and inspection on October 11, 2026. Replay took 21 minutes 16 seconds. All 1,260 statements and proofs are recursively closed, with 1,696 statement dependencies across 769 proofs. The compiled-term audit and Lax inspector agree on every dependency set, and the website projection preserves all of these links. The 208 intentional unused-helper warnings are unchanged.

## Provenance and development history

The original paper, TeX source, and earlier matching-minor proofs remain pinned to `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. [source.json](references/source.json) records the paper's SHA-256. The later complete construction has a separate immutable pin and per-file source hashes in [upstream-construction.json](references/upstream-construction.json). All reused source is Apache-2.0 licensed.

The complete construction was available in a newer upstream revision than the project's original source checkout. Its port keeps the archive environment and changes namespaces, imports, and a few mathlib lemma names and simplification steps. The compatibility patch is recorded alongside its provenance.

The independently developed local route is retained, including its checked entropy, frame, moment, realization, phase, and affine-slice results. Its previous progress notes are preserved in [local-development-checkpoint.md](references/local-development-checkpoint.md). [PROOF_PLAN.md](PROOF_PLAN.md) records the completed route and preserves the historical detailed plan; [REMAINING.md](REMAINING.md) records the remaining validation or optional integration work. Open tasks in the historical local route are not assumptions of the complete proof.
