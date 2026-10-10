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
  those tests. Occurrence of these bits and gradient realization on the
  entire cut space remain separate, open tasks.
- The effective table contraction is defined independently of chosen
  extensions and identified with the actual frame contraction. Full paired
  witness lists and scalar recipes are defined, with the fourteen-ray
  budget, diagonal sums, and matched-key tensor sharing proved.
- Numerical prescriptions for all four endpoints, independence of the actual
  incident key spans, and frozen baseline cross forms extending the tables.
  Both reciprocal endpoint roles have channel rank at most `3K+28` for the
  same baseline. The target residual vanishes on effective profiles and
  every selected atom; the whole-space annihilator argument remains open.
- Pure responses on the barred quotients of the actual nominal spaces.
  Their annihilating pairs of cut profiles have component rank at most
  `2K+28` and bounded label decompositions. Strong sparse pin exclusions
  cover arbitrary base coefficients. A selected affine-ray moment block
  is forced to be a scalar point moment. Fresh coefficients can be
  extracted through pin and key quotients and applied to the actual tensor
  blocks. Triangle relations give one scalar per selected witness on its
  tag star. Subtracting those actual atoms preserves pure annihilation and
  leaves a bounded reconstruction using only unselected labels. The full
  derivative-response reduction and table injection remain open.
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
with 128 concepts and 350 annotated proofs, 348 of which have no open
mathematical assumptions. All kernel replays pass. The only conditional
proofs are the two counterexample consequences of the open Theorem 1.1.

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
