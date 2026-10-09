# Remaining proof work

The required endpoint is Theorem 1.1, with its full transitive dependencies,
and both ordinary and fractional consequences in Corollary 1.2. No graph
with the required connected-matching bound has been constructed in Lean.
The project is not ready for submission as a complete counterexample.

See [PROOF_PLAN.md](PROOF_PLAN.md) for the detailed mathematical plan;
this file is the shorter status and acceptance checklist.

## Acceptance criteria

1. An annotated proof discharges
   `Lax342547.Counterexample.arbitrarily_large_small_connected_matching`.
2. Both counterexample consequences have a closed, acyclic Lax proof network.
   A proof that merely assumes the graph exists does not meet this criterion.
3. All paper-specific assumptions are discharged by checked proofs. No
   `sorry`, `admit`, unproved implementation axiom, opaque proof oracle, or
   native computation used as a logical axiom occurs in the proof closure.
4. `lax build . --replay` and `python3 scripts/check_completion.py` pass.
5. Review the Lax proof network against the paper's actual dependencies before
   submitting. A long argument must not be represented by one unexplained
   assumption whose name merely restates the desired conclusion.

## Dependency order

| Work | Source | Current state |
| --- | --- | --- |
| Connected matchings and literal clique-minor models | §1, §3.3 | Definitions and counting proofs ported |
| Chromatic and fractional chromatic bounds | §1, Proposition 3.5 | Proved |
| Binary hole equations, symmetry, looplessness, triangle exclusion | Definition 2.1, Lemma 2.2 | Defined and proved |
| Independence bound for sampled positions | Equation (2.2) | Proved, without assuming an injective sample |
| Boolean point moments, cut profiles, and cut kernel | §2.2–2.3, Lemma 2.3 | Projection, majority intersection, and constant-kernel proofs checked |
| Concrete tester functionals, mixer form, and self-Gram matrix | §2.3 | Complete, including cut descent, the moment identity, and Z-coordinate invariance |
| Uniform raw frames, injective tensor realization, and annihilators | §2.4, equations (2.13)–(2.16) | Concrete model assembled; frame existence, embedding, self-contraction, raw-space count, product law, and sampled-graph independence checked |
| Finite entropy projection, including the full support assertion | Lemma 3.2 | Not formalized |
| Real-capacity terminal cut with both endpoint and pair exceptions | Lemma 3.3 | Not formalized |
| Entropy-controlled fingerprints and sample probability bounds | Proposition 3.4 | Not formalized |
| Frame extension, Gram normalization, sparse intersections | §4.1–4.2 | Not formalized |
| Two peelings with exact pins and subsequent image bounds | §4.3, Lemma 4.5 | Not formalized |
| Bilinear/Walsh estimates | §4.4 | Not formalized |
| Base-moment span, selector interpolation, and low-rank label decomposition | Lemmas 5.1–5.2 | Complete; all label identities, rank bounds, and reconstruction checked |
| Sparse label supports of projected pins | Lemma 5.3 | Complete; the exact uniform label budget covers all sparse vectors |
| Atoms, flavors, and finite parameter laws | Definition 5.4 | Defined; incidence formula, role/diagonal bits, retained coordinates, and product law checked |
| Uniform mixing matrices, chosen before the unit law | §5.3, Lemma 5.5 | Not formalized |
| Scalar recipes, table flags, gradient realization | §6, Theorem 6.3 | Not formalized |
| Accepted queries and overlap-to-four-holes implication | §7, Proposition 7.1 | Not formalized |
| Phase alternatives and accepting-pair injection | §8 | Not formalized |
| Common prediction, exactification, and status preparation | §9, Proposition 9.2 | Not formalized |
| Histogram compactness, Gram comparisons, and many-query bounds | Lemmas 10.1–10.5 | Not formalized |
| Mixed-law tests, binary mixing, and unary positivity | Lemmas 10.7–10.11 | Not formalized |
| Weak product testing and factorized integration | §11 | Not formalized |
| Common subsequential limit and vanishing-overlap implication | §12 | Not formalized |
| Dual scalar system, fresh lists, and positive-mass overlap | §13 | Not formalized |
| Uniform large-set hits and inverse-polynomial overlap | §14.1–14.3 | Not formalized |
| Raw supersaturation, uniform over all admissible unit laws | Theorem 3.1, completed in §14.4 | Not formalized |
| Parameter existence and every quantitative margin | Appendix A | Not formalized |
| Supersaturation → sampled graph → arbitrarily large orders | Proposition 3.4 → Theorem 1.1 | Not formalized |
| Ordinary and fractional counterexample consequences | Corollary 1.2 | Proved assuming Theorem 1.1 |

## Next implementation steps

The concrete algebraic model and Boolean moment algebra in Lemmas 5.1–5.3
are complete. Atoms and flavor distributions are now defined on that
model. The next algebraic target is the uniform mixer theorem in Lemma 5.5;
its probability and rank estimates remain open.

1. Prove the forward/reverse matrix compatibility calculation and its
   codimension cost, then the random row-map and low-rank profile counts.
2. Establish the unary and binary mixer rank bounds simultaneously, with
   all mixers chosen before the unit law.
3. State raw supersaturation using this concrete law. Preserve the separate
   marginal caps and joint cap; the two endpoints of a unit can be dependent.
   An abstract structure with a supersaturation field is not a construction.
4. Formalize the independent finite distribution-to-graph argument of §3.1–3.2.
   It must handle multiple sampled matching edges with the same raw unit type.
5. Work through §§4–14 in the dependency order above, splitting large results
   into mathematical concepts with faithful Lax proof dependencies.

## Quantifier and scale checks

- All construction constants are fixed independently of `n` and of the unit
  law. Mixer matrices may depend on `n`, but are chosen before the unit law.
- The fixed constants start with `C₀ = 1000`, `g = 10^9 + 1`, `D = 4C₀g`,
  and `M = 2^1000`. Respect the full order in Appendix A before choosing `M₀`.
- `N = M₀n` with `M₀` fixed means `O(n)` is not `o(N)`.
- Supersaturation must give probability at least `2^(-100gN)` for two
  independent units, under the precise marginal and joint density bounds.
- Sample size is `m = 2^(1000gN)`. The count of fingerprints has logarithm
  `o(m)`; control both kinds of terminal exception before taking a union bound.
- Leaf laws before extra pairing conditions are independent. Preserve this
  independence when selecting tests and finite families of superlevel sets.
- Keep subprobability masses after filtering. Do not normalize away lost mass.
- The inverse-polynomial branch has compatibility mass of order `N^(-4)`.
  An ordinary positive-mass limit argument does not handle it.
- Every asymptotic argument needs an explicit quantified threshold. A parameter
  ledger or an informal asymptotic annotation is not a proof of that threshold.

If an attempted lemma fails, record its exact statement and obstruction here.
Do not weaken the requested endpoint or silently change the paper's quantifiers.
