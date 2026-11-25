# Local construction route before upstream integration

Saved on October 11, 2026. This is a historical checkpoint of the independently
developed route. Its open tasks do not describe the integrated upstream proof.

# Hadwiger counterexample

Working directory for a complete Lean formalization of OpenAI's
[A counterexample to Hadwiger's conjecture](references/openai/hadwiger-counterexample.pdf),
dated September 23, 2026, and its eventual Lax submission.

**Status: incomplete; not submitted.** Theorem 1.1, the existence of the
graphs, has no proof yet. The proved counting and coloring consequences do
not establish the counterexample without that construction.

The Lax identifier is `lax-342547`. The concept and proof packages already
use the archive's Lean `v4.33.0` environment and pinned mathlib revision.

The [detailed proof plan](PROOF_PLAN.md) gives the mathematical steps,
interfaces, dependency order, quantitative obligations, and completion
criteria for the entire construction. It distinguishes checked results
from planned arguments and treats the rare-overlap branch separately.

The finite no-cover part of §8 is now checked: actual exposed row/column
quotients, a deterministic greedy dyadic certificate, componentwise rank
growth, exact binary channel character averages, and even-moment/Markov
phase tails. Accepting-pair injection is now checked for the actual small
tables, including all sixteen flags per component and a channel choice
uniform over later unit laws and inverse-polynomial accepting masses.
The complete phase alternative remains open.

## Target

For every lower bound, construct a finite graph on `Fin m`, with `m` at least
that bound, satisfying

```lean
G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m
```

The downstream targets include both ordinary and fractional coloring:

```text
h(G) < 26m/75 + 2/3 < m/2 ≤ χ_f(G) ≤ χ(G), for m ≥ 5.
```

The connected matching is pairwise touching. It is not enough for the union
of the matching's edges to be connected. The clique minors are ordinary
minors with disjoint, nonempty, connected branch sets. Samples are indexed
by positions and may contain repeated raw vertices.

## Existing proofs

- Lemmas 3.2–3.3: finite entropy projection with full feasible support,
  real max-flow/min-cut, and both strict terminal exception bounds.
- The conditional entropy/container graph transfer: deterministic deletion,
  ordered fingerprint replay/count, binomial and disjoint-pair sample tails,
  repeated raw-type matching occurrences, and eventual paper parameter
  margins. `PaperGraphTransfer.paper_graph_transfer` produces sampled graphs
  with the required bounds assuming genuine raw supersaturation; the high-probability endpoint is
  checked in `PaperSampleSuccess.paper_sample_success`, under the same genuine
  supersaturation assumption.
- Proposition 3.5: the matching-minor bound, adapted from OpenAI's proof.
- The ordinary chromatic lower bound, adapted from OpenAI's proof.
- Lemma 2.2: symmetry, looplessness, and triangle-freeness of the hole relation.
- Equation (2.2): the independence bound for a graph sampled from a triangle-free
  hole relation, including samples with repetition.
- Lemma 2.3: coordinate projections of moment spaces, majority intersections
  for the cyclic tags, and the constant kernel of the unordered cut map.
- The generic descent argument for the cut-functional sums and the symmetry
  and diagonal identity for the gradient form.
- The concrete ordered testers and their cut-space descent, the ordered
  mixer form, and the self-Gram matrix. Its moment identity and invariance
  under every linear change of Z coordinates are checked.
- Raw-frame nonemptiness whenever `N ≥ 2(d+h)`, injectivity of the matrix
  tensor embedding, and the zero self-contraction identity.
- The raw-space cardinality bound; the finite uniform raw law is defined.
  Its product law across components is proved. The complete concrete
  algebraic model is constructed and connected to sampled-graph independence.
- Lemma 5.1: the exact base-moment span and selector interpolation.
- Lemma 5.2: the full low-rank label decomposition, including the Boolean
  diagonal identities, the label-count and sum-of-ranks bounds, and recovery
  of all higher-degree moments. Its proof has only Lean's standard axioms.
- Lemma 5.3: the exact uniform label budget across all sparse expansions in
  all projected pin spaces, including the paper's finite-sum formulation.
- Definition 5.4: concrete atoms and all flavor parameter domains, with
  their incidence formulas and independent uniform retained bits.
- Estimates used in Lemma 5.5: exact forward/reverse compatibility,
  the resulting density bound on free-direction observations, loss of
  at most twice the codimension under bilinear restriction, and rectangular
  low-rank factorization, counting, and uniform probability bounds.
  Symmetric factorization and the low-total-rank count are checked for
  the actual cut-profile space. The sharper row-corank probability is
  `2^(ms)/2^(sn)`. Distinct labels have independent free-direction spaces,
  giving a uniform pair of ordered mixer blocks and uniform nonempty parities
  across an independent mixer family, with the associated low-rank bounds.
  The sharp restriction of the actual self-Gram matrix, its vanishing free
  restriction, and all three sharp-parity probability bounds are checked,
  including the alternating block of side `n/2` rounded down. The affine
  change of point inputs under a base-block variation is also checked.
- The unary part of Lemma 5.5: the actual atom's affine quadratic expansion,
  exact formal polar rank, and bounded row space chosen before the non-Z
  fixing. The joint row density, corank estimate, and finite union yield
  simultaneous unary mixers for all sufficiently large `n`, with an
  explicit proved threshold under `p_* (g²+3) K ≤ s₀`. The new proofs use
  only Lean's standard axioms.
- The full Lemma 5.5: the actual bilinear parts on every flavor contain
  the checked free and sharp restrictions. Finite union bounds and the
  strengthened unary estimate yield a joint choice of every mixer before
  any unit law. `UniformMixers.exists_paper_mixers` uses the paper's
  `s₀=40(K+1)p_*(g²+5)` and `J=101(s₀+K²+1)`, with an explicit threshold
  and the exact binary rank condition `n ≤ 5 * rank`.
- Lemma 4.6: binary-character orthogonality, the exact Walsh energy identity,
  the `1 / sqrt(2^rank)` bilinear correlation bound, bounded-density factors,
  subprobability weights, and arbitrary separate phases. The vector-slot
  form has exactly `N * rank C` bits of rank. A finite conditional mixture
  theorem retains the actual cell masses and density costs.
- The ordinary fractional-coloring lower and upper bounds.
- Lemmas 4.1–4.2: the paired-frame orbit over arbitrary fields and both
  Gram normalization bounds, with the explicit quarter-factor lower bound.
- Lemma 4.3(a,b): all uniform frame marginals, the actual conditional
  minus and channel laws, their rank-failure bounds, channel transpose
  failures and joint density, and prescribed tuple orbit laws. Independent
  tuple laws allow dimensions and Gram values to vary across draws.
- Lemma 4.3(c): the full reference image cap `2^(-(1-ε)tN)` for directions
  mixing both endpoints, across both signs and all components. It uses
  actual nominal ranks, permits dependent tuples and ranks growing with n,
  and includes a single ambient scale choice paying every conditioning
  and dimension cost.
- Lemma 4.4: bounded coefficient certificates and their exact count give
  an explicit `2^(-DN/4)` intersection exception under the joint density
  cap. Shared tensor ranks, unique majority-zero representatives, the
  `4D/g` support bound, and equality of their `χStar` values are checked
  on the actual concrete profiles. One ambient scale pays every cost
  independently of n and of the unit law.
- Lemma 4.5: both finite exact-pin peelings for the actual raw frame law,
  including disjoint supports, the discarded-mass bound, nominal quotient
  ranks, bounded new dimension, normalized all-rank image caps, and joint
  density bounds. Conditional parts recover the retained law with their
  actual masses. Metadata/image counts, restriction trimming, final pin budget, and
  preservation of effective spaces are checked. Exact nested masses and
  mixed marginal normalization are tracked separately.
- The deterministic table and prescription work for Lemma 6.2: effective
  spaces have dimension at most K squared and total component rank at most
  K; table spaces, protected channel projections, private complements, and
  the four injection flags are defined. Admissibility separates into two
  unary filters on the actual frame orientations. Fresh selected rays are
  independent modulo the table spaces, with the exact sparse-label budget.
  Table counts are independent of the primal dimension; padded nominal
  coefficient records have an explicit linear-size bit count.
- Compatible row sums are realized by an explicit symmetric binary matrix.
  The coupled recipe and role equations give the required compatibility.
  `ConcreteRecipes.prescribe` chooses indexed ordered L/R bits using only
  tags, tester summaries, and opposite role/p bits, and proves the desired
  list-gradient identities for any actual atoms and mixers satisfying
  those tests. Occurrence of these bits remains a probabilistic task; deterministic
  realization on the entire cut space is now checked.
- The effective table contraction is defined independently of chosen
  extensions and identified with the actual frame contraction. Full paired
  witness lists and scalar recipes are defined, with the fourteen-ray
  budget, diagonal sums, and matched-key tensor sharing proved.
- Numerical prescriptions for all four endpoints, independence of the actual
  incident key spans, and frozen baseline cross forms extending the tables.
  Both reciprocal endpoint roles have channel rank at most `3K+28` for the
  same baseline. The target residual vanishes on effective profiles and
  every selected atom. The obstruction-space reduction is checked;
  unrestricted linear solvability and bounded derivative corrections are
  checked. Residual rank bounds, compression, and the complete gradient
  realization are checked under the actual recipe and capacity hypotheses.
- Pure responses on the barred quotients of the actual nominal spaces.
  Their annihilating pairs of cut profiles have component rank at most
  `2K+28` and bounded label decompositions. Strong sparse pin exclusions
  cover arbitrary base coefficients. A selected affine-ray moment block
  is forced to be a scalar point moment. Fresh coefficients can be
  extracted through pin and key quotients and applied to the actual tensor
  blocks. Triangle relations give one scalar per selected witness on its
  tag star. Subtracting those actual atoms preserves pure annihilation and
  leaves a bounded reconstruction using only unselected labels.
  Fresh key coefficients vanish in unselected sparse expansions. For a
  primal sparse vector, the actual barred-space decomposition reduces to
  pin membership using protected/private complementarity. Pure contraction
  tests put the unselected plus contraction in the actual primal pin.
  Allowed channel changes preserve frozen entries and vanish on opposite
  primal inputs. The full pure-plus-derivative response kills every selected
  atom and is preserved by selected subtraction. Actual rank-one derivative
  tests and both table-injection flags force the reciprocal residual
  contractions to zero. Row and column membership, sparse key removal,
  and tensor reconstruction now put the remainder in the actual effective
  profile spaces. Every full obstruction decomposes into selected atoms
  and this effective remainder. Parameter linearity and finite-dimensional
  annihilator duality construct an unrestricted response realizing the
  actual scalar-recipe residual on the whole profile-pair space.
- Allowed derivative outputs can be compressed inside their original
  perpendicular value spaces while preserving all baseline pairings.
  The actual recipe solution retains its full response and barred domain
  quotients, with both derivative ranks at most `3K+28` per component.
- The actual recipe residual has a checked per-individual matrix rank bound
  `14K+140` after removal of the projected target and derivative product.
  The initial projected pure form has rank at most the sum of the two
  target-matrix ranks. Chosen block maps fix all projected pins and keys,
  preserve the residual target, and preserve allowed moments and the actual
  cut-profile domain. They descend to barred quotients, where private
  channel directions vanish. The compressed pure correction has rank at
  most `Dquo`, with the paper's explicit block and quotient bounds.
- A pure quotient form factors through allowed channel values whenever its
  rank fits the surviving dot pairing. Orthogonality to protected channels,
  baseline values and bounded derivative values costs at most `K+2R` on each
  side. The resulting maps realize the form exactly and have the required
  vanishing cross terms. The explicit tester/mixer target routing has rank at most
  `15r₀+14J|E|`. The paper's channel margin fits the restored pure form;
  both reciprocal endpoint roles assemble simultaneously while preserving
  frozen pins and keys. All four whole-space gradients and hole witnesses
  are checked. The primal record count is `16|E|h dim(B)` bits.
- Collision dependencies: actual primal-entry tests now yield all four holes
  in an original retained-cell pair. Both image caps come from the original
  PMF leaf min-entropy; separate unary records freeze the target directions,
  and the checked gradient-realization theorem constructs the target.
  Key-indexed records recover the accepted key mass exactly. The finite
  collision inequality averages over independent parameters, permits record
  partitions depending on the opposite parameters, and includes the explicit
  pruning cost from the key-space and record counts. Actual independent leaf
  masses, skipped pairs, squared restriction recovery, bounded options, and
  quantitative exponent margins are checked. Joined pin/key records have
  explicit rank and column budgets. Completing the numerical/status record
  encoding and the paper's full asymptotic Proposition 7.1 wrapper remains.
- Finite phase estimates: actual raw-channel density transfer, uniform
  counting of targets by original total component rank, and fixed-parameter
  bounds for arbitrary endpoint groups. The whole-unit marked average is
  checked. The full phase alternative and large-cover concentration remain.
- Actual common-projection quotient factors and covered offsets are
  constructed, with their dimension budget and nonzero-difference criterion.
  Tiny-cover algebra includes the exact four even-character identity and
  inverse-polynomial four-zero mass under explicit odd-character bounds;
  those character bounds remain an open probabilistic dependency.
- Protected-channel estimates: small-subspace counts, uniform transpose
  images, adaptive protected spaces, and amplified independent pin witnesses
  are checked. `UniformTableInjection.exists_uniform_injection` now combines
  the actual admissible-table flags with the raw accepting estimate. Its
  channel dimension is chosen before the ambient dimension, unit law,
  adaptive pins, and polynomial accepting-mass exponent.
- Boolean exactification: actual selector-span nonvanishing, recovery past
  excluded labels, degree-two point-tensor evaluations, and the odd-tag
  common-atom identity. Average prediction error now gives a retained family
  with exactly one common point function. All-flavor affine-slice variance is now checked. The full
  zero-difference case and status preparation remain open.
- Quadratic character bias on actual binary functions and affine subspaces
  is checked from the polar rank. The later histogram and mixing arguments
  remain open.
- Lemma 10.2 in finite quantitative form: uniform relative Gram errors for
  growing slot ranks, additive errors across heterogeneous independent
  groups, and the half-ambient exponential bound.
- Cross-batch Gram conditioning: every nonzero reciprocal Gram character has
  at least N bits of rank; the normalized comparison uses actual uniform
  Gram-orbit batch laws and their proved density caps. The combined orbit
  is identified exactly with the separate orbits conditioned on reciprocal
  Gram entries and joint injectivity. Joint-injectivity failure is bounded
  under the actual product law and after reciprocal Gram conditioning.
  Actual primal raw and full self-channel Gram comparisons, including
  heterogeneous independent groups, are assembled. Complete mode interfaces
  and the many-query estimate remain open.
- Conditioned affine-slice comparison for every actual atom flavor,
  arbitrary bounded common tests, explicit dependence costs and uniform
  large-n thresholds. Reference comparisons transfer to empirical density
  caps with error `sqrt(L * variance)`.
- The deterministic small-slice rank contradiction, exact reference Gram
  slice marginals, and a quantitative common-test error obstruction.
  Pure synthetic slice Grams have proved positive mass from bounded tester
  prescriptions, with a floor uniform over tags and excluded sets. Their
  full variance bound is checked without assuming the Gram mass. Empirical
  synthetic-test instantiation and full Lemma 9.5 remain open.
- The ordinary and fractional counterexample consequences, **conditional on
  Theorem 1.1**, with this assumption recorded in their Lax annotations.

See [REMAINING.md](REMAINING.md) for the construction and its dependencies.
[Paper statements](references/paper-statements.json) index the numbered
declarations by their original TeX labels and source locations.

## Source and reuse

The paper, its TeX source, and the upstream partial proofs are pinned to
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Provenance and the PDF's
SHA-256 are recorded in [references/source.json](references/source.json).

`HadwigerMatching/Main.lean` in the upstream repository proves Proposition
3.5, not the existence assertion of Theorem 1.1. Its clique-minor helpers
come from `ListHadwiger/Model.lean` and `ListHadwiger/Basic.lean`; this project
extracts only the definitions and facts needed for that proposition.
The upstream family-157 formalization page describes the separate linear
list-coloring theorem. It is not evidence that this counterexample is proved.

## Build and audit

At the latest validated checkpoint, `lake build` and `lax build . --replay` pass,
with 356 concepts and 1,194 annotated proofs, 1,192 of which have closed
archive proof networks. All kernel replays pass. The only proofs with
unresolved archive dependencies are the two
counterexample consequences of the open Theorem 1.1. The finite graph
transfer has raw supersaturation as an explicit mathematical hypothesis.
The earlier mathematical estimate was about 75%. The new accepting-table
injection and Gram/affine-slice results advance that checkpoint, but the
requested 90% milestone has not been established. Declaration counts are
not used to certify a percentage.

The completed preliminary proofs report only Lean's standard background
axioms in `AxiomAudit.lean`. The completion checker must still exit with
status 1, identifying Theorem 1.1 as the unresolved dependency of both
counterexample consequences. Unused helpers are retained for the remaining
construction and integration work.

```sh
cd proofs
lake build
cd ..
lax build . --replay
python3 scripts/check_completion.py
```

Lax concept `axiom` declarations are statements awaiting annotated proofs.
They are part of the archive's normal statement format. A successful Lax build
does not mean that every statement has been proved. The completion checker
follows the inspected proof dependencies and rejects unresolved statements
and cycles. It currently must fail because Theorem 1.1 is unresolved.

The [axiom audit](proofs/Lax342547Proofs/AxiomAudit.lean) prints the exact
logical dependencies of the principal proof declarations. The two final
corollaries currently report the Theorem 1.1 concept axiom; the completed
preliminary results must report only Lean's permitted background axioms.

## Submission

Complete the construction, verify the proof network against the paper, pass
the completion check after a fresh `lax build . --replay`, and update the
abstract to describe the completed result. Then push the reviewed source to
a public GitHub repository and run `lax submit .`. Submission as a draft is
authorized; permanent registration is a separate lifecycle action.

The original paper is stored as a reference. It is not configured as a Lax
paper attachment, because its full-result claim currently exceeds the proved
scope of this project.


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
| Finite entropy projection, including the full support assertion | Lemma 3.2 | Complete finite proof, including full feasible support and the exact information-projection/support cost |
| Real-capacity terminal cut with both endpoint and pair exceptions | Lemma 3.3 | Complete finite real-flow proof and both strict exception mass bounds |
| Entropy-controlled fingerprints and sample probability bounds | Proposition 3.4 | Entropy algorithm, ordered replay/count, both sample tails, repeated-type matching transfer, and eventual paper margins checked; conditional graph existence and the high-probability endpoint checked |
| Frame laws and full reference image cap | §4.1, Lemmas 4.1–4.3 | Complete: paired orbits, normalization, conditional laws, tuple laws, density bounds, and the all-rank two-endpoint reference cap with uniform scale choice |
| Sparse intersections and representatives | §4.2, Lemma 4.4 | Complete: explicit exponential exception, exact coefficient count, shared-tensor ranks, unique majority-zero representatives, support and chiStar bounds, and a uniform concrete scale |
| Two peelings with exact pins and subsequent image bounds | §4.3, Lemma 4.5 | Complete in quantitative finite form: both partitions, restriction trimming, metadata/image count, preserved pins and effective spaces, final rank budget, image/density bounds, mixed marginal costs, and actual-mass recovery |
| Bilinear/Walsh estimates | §4.4, Lemma 4.6 | Complete: exact energy identity, bilinear-rank bound, densities, subprobability masses, separate phases, bit rank, and finite conditional mixtures |
| Base-moment span, selector interpolation, and low-rank label decomposition | Lemmas 5.1–5.2 | Complete; all label identities, rank bounds, and reconstruction checked |
| Sparse label supports of projected pins | Lemma 5.3 | Complete; the exact uniform label budget covers all sparse vectors |
| Atoms, flavors, and finite parameter laws | Definition 5.4 | Defined; incidence formula, role/diagonal bits, retained coordinates, and product law checked |
| Uniform mixing matrices, chosen before the unit law | §5.3, Lemma 5.5 | Complete: simultaneous unary rank/row spaces and all binary parities on every flavor, explicit large-n threshold, and the paper's mixer parameters |
| Scalar recipes, table flags, gradient realization | §6, Theorem 6.3 | Effective dimension/rank bounds, table spaces and injection flags, private complements, unary admissibility, fresh-key independence, coefficient/table counts, concrete atom prescriptions, effective contractions, and full paired recipes checked; all four endpoint prescriptions, frozen baselines of rank at most 3K+28, and residual vanishing on effective/selected profiles checked; whole-space realization, frozen assembly, all four holes, and primal record count checked under the genuine recipe and capacity hypotheses |
| Accepted queries and overlap-to-four-holes implication | §7, Proposition 7.1 | Finite collision core checked: actual primal-entry/target instantiation and all four holes in original PMF cells, both all-rank leaf image caps, key-indexed unary records, independent parameter and actual leaf-mass averaging, skipped pairs, pruning/scalar exponents, squared restriction recovery and bounded-option costs; complete numerical/status metadata encoding, uniform record budget/target selection and the full asymptotic Proposition 7.1 wrapper remain |
| Phase alternatives and accepting-pair injection | §8 | Finite no-cover rank growth, actual channel moments and tails, raw-law density transfer, sharp total-rank target count, and fixed-parameter endpoint-group bounds with whole-unit marks checked; actual quotient factors/covered offsets, four even-character algebra, and independent protected pin-witness estimates checked; actual accepting-table injection and its uniform early channel choice checked; full alternative, odd-character bounds, large-cover concentration, and preparation remain |
| Common prediction, exactification, and status preparation | §9, Proposition 9.2 | Boolean nonvanishing, excluded-label recovery, actual point-tensor degree, odd-tag common-atom algebra, and retained common prediction from average error checked; actual all-flavor conditioned affine-slice variance and uniform thresholds checked; deterministic zero-difference rank obstruction, synthetic common-test error transfer, actual reference slice marginals and pure synthetic Gram mass checked; empirical synthetic-test instantiation, full zero-difference argument and preparation remain |
| Histogram compactness, Gram comparisons, and many-query bounds | Lemmas 10.1–10.5 | Quantitative Gram normalization (10.2) checked; actual reference-batch density and conditioned Fourier comparison checked; actual primal raw comparisons and full self-channel Gram fiber comparisons, including heterogeneous independent groups, checked; the complete mode interfaces, many-query estimate and histogram nets remain |
| Mixed-law tests, binary mixing, and unary positivity | Lemmas 10.7–10.11 | Actual quadratic polar-rank bias and affine-subspace bias checked; full mixed-law estimates remain |
| Weak product testing and factorized integration | §11 | Not formalized |
| Common subsequential limit and vanishing-overlap implication | §12 | Not formalized |
| Dual scalar system, fresh lists, and positive-mass overlap | §13 | Not formalized |
| Uniform large-set hits and inverse-polynomial overlap | §14.1–14.3 | Not formalized |
| Raw supersaturation, uniform over all admissible unit laws | Theorem 3.1, completed in §14.4 | Not formalized |
| Parameter existence and every quantitative margin | Appendix A | Not formalized |
| Supersaturation → sampled graph → arbitrarily large orders | Proposition 3.4 → Theorem 1.1 | Conditional sampled-graph existence checked at the paper parameters; actual supersaturation and final arbitrarily large construction remain open |
| Ordinary and fractional counterexample consequences | Corollary 1.2 | Proved assuming Theorem 1.1 |

## Next implementation steps

The previous mathematical checkpoint was estimated at about 75%. The current
working estimate is about 80%, with a plausible range of 75–85%, weighted by
remaining mathematical difficulty. This is an estimate, not a certified
percentage; the requested 90% checkpoint is not yet established. The initial
October 11 work added 37
closed annotated endpoints, recorded below by their mathematical content
rather than used to infer a completion percentage. The conditional finite
transfer is
checked in `PaperGraphTransfer.paper_graph_transfer`; it assumes the genuine
uniform raw supersaturation property and does not prove Theorem 1.1. The
high-probability graph-success bound is now checked in
`PaperSampleSuccess`. The finite no-cover rank-growth lemma, actual channel
moments/tails, raw-law density transfer, sharp target count by original total
component rank, and fixed-parameter endpoint-group phase bounds are checked,
including whole-unit marked averages. Actual common-projection quotient
factors and covered offsets are constructed. Tiny-cover four-zero mass is
checked under explicit bounds on the twelve odd characters; proving those
bounds remains necessary. Protected-subspace counting and independent pin
witness estimates are checked. Actual accepting-table injection now
controls all sixteen flags per component, with the channel size fixed
before the ambient dimension, polynomial mass exponent and unit law. Its
finite hypotheses include the accepting-family count, separate marginal
caps, adaptive pin rank, and actual table admissibility. Average error now
exactifies actual degree-two point predictions on a
retained family. The all-flavor affine-slice variance transfer is now checked. The empirical
synthetic-test instantiation in the zero-difference case, status preparation,
and large-cover concentration remain major dependencies.
Actual quadratic polar-rank bias on affine subspaces is also checked.

`HistogramGram` proves uniform relative Gram normalization errors, including
heterogeneous products and ranks up to half the ambient dimension.
`CrossGramBasis` proves that the two reciprocal Gram blocks have no zero
nontrivial character; `GramOrbitDensity` supplies actual reference-law caps
and their conditioned bounded-test comparison. `JoinedGramOrbits`
identifies the combined orbit and its exact filtered law.
`JointGramInjection` bounds joint-injectivity failure under those actual
reference laws, including after reciprocal Gram conditioning.
`RawBatchComparison` now performs the exact law integration and bounded-test
comparison. `RawFrameComparison` connects this to actual primal raw frames
and full self-channel Gram fibers, with a threshold depending only on the
four column counts and an explicit constant over `sqrt(2^N)`.
`GroupTensorComparison` adds the errors across heterogeneous independent
groups without restricting the global tests to products. `RawGroupedComparison`
instantiates the result for the actual grouped raw observations, retaining
varying Gram matrices and column dimensions. These cover primal raw laws
and specified full Gram fibers; complete unconditioned mode interfaces still
need to be verified against the paper.
`AffineSliceIndependence` proves the actual point-column dependence bound
and that the nominal Gram ignores every free coefficient. `EmpiricalVariance`
proves the finite second-moment assembly under explicit mean and pair
comparison hypotheses. The resumed session now discharges these hypotheses
in `AffineSliceVariance`: the reference mean comes from actual primal orbit
laws, and the pair estimate comes from actual grouped raw comparison.
`FlavorAffineSlices.flavor_slice_variance` applies the full conditioned
coefficient law to generic, shared-only and every pure flavor, without
conditioning the excluded coordinates inside a larger uniform law. The
variance budget is

`#S * RawFrameComparison.errorBound + 4 * 2^(2d+1-n) / beta^2`.

`AffineSliceScales.uniform_threshold` supplies every comparison margin and
any positive variance tolerance before selecting laws, Grams or tests.
`CommonTestTransfer` transfers these moments to capped empirical unit laws,
with comparison error at most `sqrt(L * variance)`.

The zero-difference argument now has the following checked dependencies:

- `SmallSliceRank` selects actual rank witnesses, proves the global rank bound
  from every small coordinate slice, and bounds cross-coefficient rank by
  twice the number of affine products. Its parity endpoint contradicts a
  larger identity matrix.
- `SyntheticRankTransfer` assembles parity and all slice tests on one common
  reference law. Separate empirical caps and centered variance bounds force
  total prediction/comparison error at least one; a fixed positive error
  margin depends only on the finite test count and density cap. This theorem
  is conditional on the actual test couplings, not a proof of Lemma 9.5.
- `OrbitSliceLaw.slice_uniform` proves the exact uniform marginal law of any
  injective coefficient restriction of the full reference Gram orbit.
- `FixedSelectorGram` cancels the sharp contribution at a fixed selector and
  identifies the Gram with retained tester coordinates. Independent tester
  prescriptions have exactly `2^(-#slots * #columns)` mass; routing uses
  all retained blocks, not just one block.
- `PureTesterRoom` counts exactly `k * (2k+1-|T0|) * r` retained pairs for the
  paper's pure flavor. Its positive real Gram floor is uniform over the tag
  and excluded set and independent of n and the unit law.
- `TesterProductRouting` realizes sums of any bounded number of Gram products
  using that many distinct tester pairs. `SyntheticGramSlices` constructs
  the actual ordered synthetic slice Gram and realizes it using q pairs for
  q selected coordinates in each half. `pure_slice_variance` combines the
  actual Gram mass proof with the full flavor variance theorem; it needs
  neither a stronger room bound for all 2q+1 affine columns nor an assumed
  positive mass for the prescribed Gram event.

These additions comprise 50 annotated endpoints in 11 new concept/proof
module pairs. The previous five resumed module pairs (`RawBatchComparison`,
`RawFrameComparison`, `GroupTensorComparison`, `RawGroupedComparison`, and
`ConditionedAffineColumns`) and all earlier changes are preserved. Full
Lean compilation and the axiom audit use only the standard background
axioms for these new proofs. Fresh archive replay is being verified; the
previous saved replay also succeeded. Theorem 1.1 remains unproved.

The next concrete integration steps are:

1. Instantiate the actual synthetic key array, its point and coordinate-slice
   restrictions, and the common predictor tests in Lemma 9.5. Use the exact
   orbit marginal, pure synthetic Gram floor and variance bounds above.
   Derive empirical parity from the shared-only common-atom identity and
   local products from the marked tester/low-rank predictions, with every
   fixed conditioning and density cost. Only then apply
   `SyntheticRankTransfer.prediction_error_budget` to eliminate unequal
   diagonal coefficients when Delta = 0. Generic conditioned variance alone
   does not establish these empirical-success hypotheses.
2. Complete the twelve odd-character bounds, large-cover concentration and
   actual phase alternatives; assemble full status preparation and the
   remaining numerical/status metadata for Proposition 7.1. Verify every
   complete mode interface against the paper before closing Lemma 10.3.
3. Continue to the many-query estimate and histogram nets; retain the
   growing-rank normalization denominators. The later common-limit,
   product-testing, dual scalar, uniform supersaturation and Appendix A
   parameter arguments remain open.

The concrete algebraic model, Lemmas 5.1–5.3, and the full uniform
mixer theorem in Lemma 5.5 are complete. The endpoint
`UniformMixers.exists_paper_mixers` chooses all matrices before any unit law
and proves the unary and binary properties with the paper's mixer parameters.

1. The two peeling stages of §4.3 are complete in quantitative finite form.
   The endpoint `ImageScale.reference_image_cap`
   gives `2^(-(1-ε)tN)` for the actual summed ranks, including arbitrary
   dependent tuples and ranks growing with n. `exists_paper_scale` pays
   every density and dimension cost with one M₀ independent of the law.
   `SparseIntersections.raw_intersections` now proves all conclusions of
   Lemma 4.4, with exception at most `2^(-DN/4)`. Its concrete scale choice
   pays the bounded coefficient-description count independently of the law.
   `RawPeeling.raw_peeling` now proves the finite disjoint partition and
   normalized all-rank image bounds, preserving initial pins and retaining
   actual leaf masses. `RestrictedLeaves.restricted_family` proves the
   trimming bounds for a combined restriction of mass at least `2^(-ηN)`.
   `RawSecondPeeling.raw_second_peeling` bounds discarded metadata fibers
   by `2^(-N/2)` and provides fresh leaves within the paper's final K budget.
   `MixtureRecovery` charges relative losses with the actual fiber masses.
   `ProjectedPins.effective_mono` preserves old effective spaces.
   All three Walsh
   estimates in Lemma 4.6 are now checked, including a conditional mixture
   version that preserves the actual cell masses.
2. The effective bounds, table spaces, private/protected decomposition,
   injection flags, unary admissibility, and fresh-key independence are
   checked. `ConcreteRecipes.prescribe` constructs formal L/R prescriptions
   from numerical data and proves their concrete list-gradient identities.
   Table counts and padded nominal coefficient records have explicit bit
   bounds. Effective table contractions and their raw-frame identification
   are checked. The full paired-list and scalar-recipe interface, diagonal
   sums, fourteen-ray budget, and matched-key tensor sharing are checked.
   Numerical prescriptions now cover all four endpoints. The actual incident
   key spans are disjoint from the tables and have dimension at most 28.
   Frozen baseline cross forms extend those tables and have reciprocal
   channel ranks at most `3K+28`. The target residual vanishes on effective
   profiles and all selected atoms. The full obstruction is now proved
   to lie in this space. The actual pure
   response now gives component rank at most `2K+28` and a bounded label
   decomposition. Strong sparse exclusions and the scalar selected-moment
   lemma are checked. Fresh coefficient extractors through pin and key
   quotients now isolate actual selected tensor blocks. Triangle consistency
   gives one scalar per witness across its tag star. Subtracting those
   atoms preserves pure annihilation and leaves only unselected labels,
   with the original support and sum-of-block-ranks budgets. The full
   pure-plus-derivative response is assembled and kills every selected atom;
   selected subtraction preserves it. Both sparse reciprocal contractions
   belong to their actual primal pins. Rank-one derivative tests and the
   actual row/column injection flags force both contractions to zero.
   Vanishing contractions give row and column membership; sparse key removal
   and tensor reconstruction prove the effective remainder. Finish the
   metadata format. Parameter linearity and annihilator duality are checked,
   giving an unrestricted solution for the actual recipe residual on the
   whole profile-pair space. Allowed output projections now preserve this
   entire response with both derivative ranks at most `3K+28`, retaining
   the actual quotient domains and perpendicular value spaces. The actual
   recipe remainder now has per-individual matrix rank at most `14K+140`.
   The initial projected pure form has rank bounded by the sum of the two
   target-matrix ranks. Chosen block maps preserve the target, projected
   pin/key vectors, allowed moments, and the cut-profile domain. Compression
   through the actual barred quotients yields the paper's `Dquo` bound and
   preserves the entire recipe response. Allowed pure factorization and the
   pairing capacity loss `2K+4R` are checked, including vanishing cross terms.
   The explicit tester/mixer routing bound `15r₀+14J|E|`, the channel
   margin, nonlinear correction, reciprocal assembly, and frozen constraints
   are now checked. `GradientRealization.realize` constructs the cross forms
   from the actual scalar recipe and binary prescriptions; `FourHoles`
   supplies the four witnesses. `PrimalRecords` proves the exact entry count
   and that matching records determines every required contraction.
   The finite collision core of §7 is now checked. `RawRetainedCells` and
   `ActualCellCollision` construct the target and prove four actual holes
   inside unchanged PMF cells. `FiniteCollision` accounts for independent
   parameters and record pruning; `LeafCollision` averages the original
   independent leaf masses, permits skipped pairs, and recovers the original
   law with the squared restriction cost. `CollisionCosts` and
   `CollisionScales` prove the numerical margins and bounded-option costs.
   Finish the complete numerical/status metadata encoding and its uniform
   count, select targets consistently for every actual record cell, and
   assemble Proposition 7.1 with its full asymptotic quantifiers.
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
