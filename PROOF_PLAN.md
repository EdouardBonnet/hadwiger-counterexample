# Detailed plan for a self-contained Lean proof

This is a mathematical and formalization plan, not a plan for organizing
pull requests. The objective is to prove the paper's graph-existence
theorem and close all its dependencies. It is not achieved yet.

The source of truth is the pinned September 23, 2026 paper in
[references/openai](references/openai/paper-citation.md), especially its TeX source.
[paper-statements.json](references/paper-statements.json) records all 73
numbered declarations, including nine remarks that share the theorem
counter, with the paper's numbering and source locations.
The file names in the source are offset from the section numbers after
§3; this plan always uses the **printed section and theorem numbers**.

Statements described below as targets or proposed interfaces have not
thereby been proved. Each must be expanded into a precise Lean statement
and checked against its consumers before its implementation is accepted.

## 1. What counts as completion

For every `lowerBound : ℕ`, prove that there exist `m ≥ lowerBound` and
`G : SimpleGraph (Fin m)` such that

```lean
G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m
```

From this, prove the ordinary and fractional counterexample statements
already in the project. The terminal proof must use the actual graph,
the actual meaning of a pairwise touching matching, and the actual
clique-minor and coloring definitions. Its Lean axiom closure must contain
only the ordinary background axioms used by mathlib, such as `propext`,
`Classical.choice`, and `Quot.sound`.

An abstract result that assumes supersaturation is useful as an
intermediate lemma. It is not a construction. Likewise, a structure with
a field asserting the desired graph-existence theorem is not a solution.
Lax concept declarations may state open theorems, but the final proof
network must discharge all of them without cycles.

The closing checks are:

1. Build every concept and proof module with the pinned Lean and mathlib.
2. Print the axiom closures of the actual final proofs.
3. Run `lax build . --replay`.
4. Run `python3 scripts/check_completion.py` on that fresh output.
5. Review the theorem statements and dependency graph against the paper.
6. Only then submit this as a full proof to Lax.

## 2. Present position

| Part | Current position |
| --- | --- |
| Matching/minor counting, Proposition 3.5 | Checked proof ported from upstream |
| Ordinary and fractional coloring bounds | Checked |
| Abstract hole relation and Lemma 2.2 | Checked |
| Sampled-position independence bound, including repetition | Checked |
| Moment coordinate projections, cyclic majority intersection, cut kernel | New checked proofs of Lemma 2.3's algebraic content |
| Concrete testers and their cut-space descent | Checked, with the paper's ordered coordinate pairs |
| Symmetry and diagonal of the concrete gradient form | Checked for the ordered mixer sum |
| Self-Gram moment identity and Z-coordinate invariance | Checked on the actual coordinate space |
| Matrix frame existence, tensor embedding, and finite raw-space count | Checked, including the product law across components |
| Base-moment span and selector interpolation, Lemma 5.1 | Complete checked proofs |
| Low-rank label decomposition, Lemma 5.2 | Complete checked proof, including the sum-of-ranks bound |
| Uniform sparse pin label budget, Lemma 5.3 | Complete checked proof, over all sparse vectors in all projected spaces |
| Entire concrete model, with the paper's testers and arbitrary mixers | Constructed; sampled graphs have independence number at most two |
| Atoms, flavors, and their finite parameter laws | Defined; component formulas, retained coordinates, and product law checked |
| Mixer compatibility, observation density, rank loss, profile and row-corank counts | Checked, including the actual cut profiles |
| Ordered random mixer evaluations at distinct labels | Joint uniform law, family parity laws, and low-rank probabilities checked on the free directions |
| Self-Gram binary parities | Concrete sharp/free restriction identities and the three sharp-parity probability bounds checked |
| Uniform mixers, Lemma 5.5 | Complete: simultaneous unary and binary conclusions, every flavor, explicit threshold, and the paper's mixer parameters |
| Walsh estimates, Lemma 4.6 | Complete: rank-dependent correlation, bounded densities, subprobability weights, separate phases, and the vector-slot bit rank |
| Paired-frame orbit, Lemma 4.1 | Complete over arbitrary fields, including the concrete matrix inverse-transpose identities |
| Gram normalization, Lemma 4.2 | Complete: exact Gram law, conditional rank failure, both probability bounds, and the explicit quarter-factor lower bound |
| Frame marginals and conditional laws, Lemma 4.3(a) | Uniform marginals, conditional independence, affine minus-column law, both rank-failure bounds, channel transpose failures, and joint channel density checked |
| Prescribed tuple images, Lemma 4.3(b) | Uniform paired-orbit laws for primal tuples and full tuples at fixed channel Gram; product laws permit varying tuple dimensions |
| Full reference image cap, Lemma 4.3(c) | Checked for arbitrary actual nominal ranks, dependent tuples, both endpoints and signs, and all components, including a single scale choice paying every cost |
| Sparse intersections and representatives, Lemma 4.4 | Complete: bounded coefficient certificates, explicit exponential exception, tensor ranks, unique majority-zero representatives, support bound, trace/chiStar identity, and a uniform concrete scale |
| Both exact-pin peelings, Lemma 4.5 | Checked finite partitions, quotient ranks, restriction trimming, metadata/image counts, final pin budget, preserved effective spaces, all-rank leaf caps, and actual-mass recovery; mixed marginal costs tracked separately |
| Table coordinates and atom prescriptions, Lemma 6.2 | Effective dimension/rank bounds, protected/private channels, unary admissibility, fresh-key independence, table and nominal-coefficient counts, effective contractions, paired lists, and the concrete numerical-to-atom-gradient prescription theorem checked; all four endpoint prescriptions and the bounded baseline checked; whole-space realization remains |
| Entropy/containers and the probabilistic construction | Not proved |
| Theorem 1.1 | Open |
| Counterexample corollaries | Checked only conditional on Theorem 1.1 |

Numbered steps can measure checklist progress, but they are not equal units
of difficulty or time. The October 7 moment-algebra work completed all seven
steps in §8.1; substantial parts of the construction remain open.
The October 9 work completes the concrete algebraic model in §4 and all
five steps of §8.2. The full uniform mixer theorem is now checked, including
the actual flavor bilinear parts, both finite unions, a joint choice, and
the paper's displayed mixer parameters. All four Walsh steps in §6.2 are
also checked, including a finite conditional mixture estimate retaining
cell masses. The marginal and conditional frame laws in Lemma 4.3(a,b)
are now checked, with explicit density constants and rank losses. The full
reference image cap in Lemma 4.3(c) is also checked, including the all-rank
quantifiers and the ambient scale choice. Lemma 4.4 is also checked on the
actual concrete moment profiles, with an explicit `2^(-DN/4)` exception
bound and one ambient scale independent of n and of the unit law. The
two finite peelings are checked, including restriction trimming, exact
metadata/image counts, both absolute density costs, the paper's final
pin budget, and preservation of old effective spaces. The mixed marginal
normalization and successive-restriction identities are checked separately.
The finite graph transfer and the later construction remain open.

After the full derivative response and two contraction tests, overall completion
is estimated conservatively at **about 37%**, weighted by remaining mathematical
difficulty rather than declaration count. The validated archive contains
134 concepts and 380 annotated proofs, with 378 closed proof networks.
The two remaining conditional proofs are the consequences of the open
graph-existence theorem. The requested 50% milestone has not been reached.

## 3. Fix the common mathematical interfaces

The implementation should have one representation of each object. Before
building the probability argument, settle the following interfaces.

### 3.1 Finite geometry

- Scalars: `ZMod 2`.
- Tags: `ZMod (2 * k + 1)`, specialized to `g = 10^9 + 1`.
- Components: two-element finite sets of tags, rather than ordered pairs.
  This prevents an accidental factor of two in component counts or ranks.
- Base coordinates: the `O_{d,t}` blocks and the three common blocks
  `S`, `#`, and `Z`, each with `n` coordinates.
- Selector coordinates: squarefree monomials of degree at most `jStar`.
- Coefficient vectors: functions on selector/base coordinate pairs.
- Moments: matrices on those coefficient coordinates.
- Cut profiles: the image of the actual map from allowed representative
  tuples to unordered-pair sums. Do not replace this image with an
  unrelated vector space of the same dimension.
- Raw vertices: a finite product of valid matrix frames. A frame records
  both combined-frame injectivity conditions and all three Gram equations.

### 3.2 Probability and filters

Use finite probability mass functions for raw vertices, units, and leaves.
Provide real-valued finite sums for expectations, event probabilities,
densities, and relative entropy. Prove the conversion lemmas once, so
later arguments do not repeatedly mix real and extended-real conventions.

A unit is an ordered pair **with no internal hole**. Its two endpoints may
be dependent. Two draws of a unit law are independent; this does not mean
that its four endpoints are independent.

An admissible law must expose all three pointwise caps separately:

\[
\sigma_1\le M\mu,\qquad \sigma_2\le M\mu,\qquad
\sigma\le 2^{DN}(\mu\otimes\mu).
\]

Filtered key distributions are subprobabilities. Their densities retain
their original mass. Introduce explicit restriction/normalization lemmas
with the normalization cost as a hypothesis and conclusion; never hide
it inside the query definition.

### 3.3 Parameters and quantifiers

The intended outer quantifier order is:

1. Choose all construction constants, independently of `n` and of the law.
2. For every sufficiently large `n`, choose mixers satisfying their
   uniform requirements.
3. Define the resulting raw space and reference law.
4. Quantify over **every** admissible unit law for that model.

Thus the supersaturation result must have a threshold independent of
the unit law. A theorem with a law-dependent onset is insufficient.

Use `Filter.Eventually`/`Tendsto` or explicit quantified thresholds for
asymptotics. For every error term, record which constants its bound may
depend on. Since `N = M₀ n` with fixed `M₀`, an `O(n)` cost is generally
not `o(N)`; it is paid by choosing `M₀` sufficiently large.

## 4. Finish the concrete algebraic model — §2

**Required inputs:** finite-dimensional binary linear algebra and matrices.

1. **Complete.** Specialize `MomentSpace.point` to the squarefree selector evaluations.
   Prove the coefficient count
   `pStar = ∑ j ≤ jStar, b.choose j` and the base dimension.
2. **Complete.** Instantiate `TagGeometry.allowedBase` for the paper's `O,S,#,Z`
   coordinates. The majority-intersection and cut-kernel proofs are now
   available; connect them to this specialization.
3. **Complete.** Define each ordinary tester and the shared tester by selecting the
   indicated ordered matrix entries and summing the `r₀` pairs. Prove
   their evaluation formulas on point moments.
4. **Complete.** Show ordinary testers vanish on `WStar`. Apply the representative-sum
   invariance theorem to construct genuine linear functionals `a_t`,
   `a`, and `b_t` on the cut space, using quotient/range descent.
   Keep `χStar` a function of a **representation**, as in the paper.
5. **Complete.** Define `T⁰`, `B¹`, `T¹`, and `T`. Instantiate `GradientForm` to obtain
   symmetry and `T x x = a x`. Record the ordered components in `B¹`.
6. **Complete.** Define the ordered tester matrix and `E#`, using selector degree one.
   Prove `⟨E,w⟩ = η(w)` for every `w ∈ W`, and prove invariance under
   every invertible change of the free `Z` coordinates.
7. **Complete.** Assemble the matrix frames, finite raw space, and uniform law.
   Use the explicit frame construction to prove nonemptiness for
   `N ≥ 2(d+h)`. Prove the product law across components and the bound
   `|Ω| ≤ 2^(2|E|N(d+h))`.
8. **Complete.** Restrict the checked tensor embedding to the cut space and produce
   the actual `HoleData`. Instantiate the checked hole and sampling
   results to obtain `indepNum ≤ 2` for every sample.

**Exit condition:** a concrete `Model` can be constructed from arbitrary
parameter values satisfying the elementary dimension conditions and
arbitrary mixer matrices. The model's independence bound is a closed
proof. No connected-matching claim is attached to arbitrary mixers.

The checked [`exists_model`](proofs/Lax342547Proofs/ConcreteModel.lean)
meets this condition. Its profile space is proved equal to the original
restricted cut image. The self-Gram matrix is constructed from the
ordered tester and selector-dependent # forms, and its invariance is
proved for every linear Z-coordinate change. The model records its
actual tensor embedding, contractions, gradient, and uniform law.
Only standard Lean background axioms occur in its proof closure.

## 5. Prove the finite supersaturation-to-graph argument — §3

This part can be developed for a generic finite raw space and symmetric,
loopless, triangle-free hole relation. It must later be applied to the
model from §2.

### 5.1 Entropy projection, Lemma 3.2

1. Define finite relative entropy with the zero-mass convention.
2. Establish nonnegativity using `log t ≤ t - 1` on positive support.
3. Prove continuity on the finite simplex when the reference law is
   strictly positive. Obtain a minimizer on a compact feasible set.
4. Prove the **full feasible support** property: if a feasible law assigns
   positive mass where the minimizer is zero, perturb toward that law.
   Isolate the new-support `t log t` term and show it outweighs all terms
   with bounded derivative. An informal derivative of `-∞` is not enough.
5. Now differentiate toward any feasible law on the common support.
   Derive the variational inequality and the exact entropy decomposition.
6. For a law supported on `S`, compare with the normalized restriction
   of the minimizer and conclude the increment is at least `-log ρ(S)`.

**Pitfalls:** missing support points; zero denominators; differentiating
before support has been established; treating strict positivity as closed.

### 5.2 Real-capacity terminal cut, Lemma 3.3

1. Build the finite source/left/right/sink network with the three caps.
2. Prove equivalence between a flow of value one and a feasible law.
3. Obtain a maximum flow by compactness of the finite real flow polytope.
4. Prove that a residual source-to-sink path would improve the flow.
   Use a simple finite path and the minimum of its positive residuals.
5. Let the cut be residual reachability. Sum conservation to identify
   its capacity with the maximum flow value.
6. Extract both endpoint exceptions and the pair exception. Keep the
   strict conclusions `μ(S) < 1/M` and `μ²(E₀) < 2^(-DN)`.

**Pitfall:** an integer-capacity max-flow theorem cannot silently stand in
for the needed real-capacity result.

### 5.3 Fingerprints and sampling, Proposition 3.4

1. Define the conflict graph on units: adjacency means four cross holes.
2. Define the deterministic residual algorithm, including deterministic
   choices of entropy minimizers and maximizing vertices.
3. Prove termination, preservation of the independent set, and that a
   recorded vertex cannot be selected again while the residual is feasible.
4. Bound the number of recordings by the entropy budget divided by
   `-log(1-εN)`, allowing the final infeasible step.
5. Prove replay from the fingerprint determines the terminal container.
6. Count fingerprints and prove their logarithm is `o(m)` using
   `εN = 2^(-100gN)` and `m = 2^(1000gN)`.
7. Prove the bad-position binomial bound and the disjoint-pair exception
   bound. The latter uses independence only for disjoint sample positions.
8. Union bound over containers and show the total failure probability is
   eventually less than one. This gives existence of a good sample.
9. Map a touching matching to its **set of unit types**. Permit different
   matching edges to have the same type. Count occurrences using disjoint
   sample positions, not injectivity of this map.
10. Convert the resulting matching-size bound to the defined maximum
    `connectedMatchingNumber`.

**Exit condition:** a closed conditional theorem whose only substantial
input is the precisely stated raw-supersaturation property, plus explicit
parameter inequalities. This closes the whole finite transfer, not Theorem 3.1.

## 6. Reference frame laws and Walsh estimates — §4.1 and §4.4

### 6.1 Orbit and exact finite counts, Lemmas 4.1–4.3

1. **Complete.** Prove the paired-frame orbit theorem by extending an isomorphism on
   the intersection with the pairing kernel, then matching complementary
   lifts. Verify that the resulting map and inverse transpose satisfy
   both frame identities.
2. **Complete.** Prove the Gram probability bounds by exposing the plus vectors and
   then the minus columns. Bound rank failure by a union over nonzero
   coefficient vectors.
3. **Complete.** Identify the marginal and conditional laws of primal and channel
   frames, using orbit uniformity and equal completion counts.
4. **Complete.** Prove conditional independence of the two channel draws given `P,Q`.
   It is a different claim from independence of all four frame maps.
5. **Complete.** Prove the reference exact-image cap for a tuple with total nominal
   rank `t`, measured in the direct sum of both endpoints and both signs.
   Keep the bound uniform for every possible `t`, including `t = O(n)`.
6. **Complete.** Expose the fixed conditioning factors and the loss of `2(d+h)`
   dimensions. Pay them using `M₀` and a sufficiently large `n`.

[`PairedFrames`](proofs/Lax342547Proofs/PairedFrames.lean) proves the full
paired orbit without assuming a nondegenerate Gram matrix. Its extension
argument splits the evaluation surjections, matches their kernel injections,
and corrects the remaining difference by a shear. The matrix version gives
both inverse identities and the exact primal and dual actions.
[`FrameSymmetry`](proofs/Lax342547Proofs/FrameSymmetry.lean) uses bijections of
completion fibers to prove the uniform combined-plus, combined-minus, X,
and Y marginals. It also proves the full raw-frame orbit at fixed channel Gram.
[`ConditionalChannels`](proofs/Lax342547Proofs/ConditionalChannels.lean)
identifies the fixed-P,Q fiber with the Cartesian product of its X and Y
completion spaces, proves the pointwise product law, and connects it to
filtering and renormalizing the actual raw law.
[`AffineImages`](proofs/Lax342547Proofs/AffineImages.lean) proves the exact
`2^(-t dim S)` cap for arbitrary-rank nominal tuples of independent affine
columns sharing a translation subspace S. It also gives the dependence
bound `2^(number of columns - dim S)` and the corresponding failure bound
for extending a fixed injective map. The raw-frame conditional laws and
their individual conditioning costs are now checked. The product image
theorems below combine both endpoints and signs and pay all losses,
completing steps 5 and 6.

[`GramColumns`](proofs/Lax342547Proofs/GramColumns.lean) proves that an
injective p-frame induces the exactly uniform p-by-q Gram law. It
identifies each fixed-Gram fiber with independent affine columns parallel
to the plus annihilator, and proves the conditional minus-rank failure
bound `2^(p+q-N)`.
[`GramNormalization`](proofs/Lax342547Proofs/GramNormalization.lean)
integrates these conditional laws to prove both bounds of Lemma 4.2,
including both individual injectivity requirements. It also proves the
explicit lower bound `2^(-pq-2)` under `p+q+1 ≤ N`. The extended-real
subtractions are truncated at zero; under the paper's dimension
hypothesis they agree with the displayed nonnegative lower bound.

[`InjectiveFrames`](proofs/Lax342547Proofs/InjectiveFrames.lean) proves the
uniform injectivity conditioning factor and the channel transpose bound
`2^(q+1-h)`, including its application to both actual raw-channel marginals.
[`ChannelDensity`](proofs/Lax342547Proofs/ChannelDensity.lean) proves equality
of channel masses on Gram orbits and the density cap `2^(h²+2)` per
component, hence `2^(|E|(h²+2))` for the full reference law.
[`FrameTuples`](proofs/Lax342547Proofs/FrameTuples.lean) proves the primal
and channel-inclusive tuple laws on their prescribed Gram orbits. The
full-tuple theorem is connected to filtering the actual raw law at its
self-channel Gram. Product laws allow both tuple dimensions and Gram
values to vary across independently drawn vertices and components.

[`ConditionalMinus`](proofs/Lax342547Proofs/ConditionalMinus.lean) identifies
the raw law at fixed P,X with the product of its two affine Gram fibers,
restricted only by combined minus injectivity. It proves the failure
bound `2^(2(d+h)-N)` and a factor-two event bound under
`2(d+h)+1 ≤ N`. `GramColumns.extension_failure` and
`ConditionalChannels.channel_rank_failures` give `2^(2d+h-N)` for each
channel before its separate injectivity conditioning at fixed P,Q.

[`ProductImages`](proofs/Lax342547Proofs/ProductImages.lean) proves the exact
independent-column image law in the nominal direct sum of all draws and
the injective-frame conditioning bound. It also extracts an independent
tuple of exactly the rank of an arbitrary coefficient matrix.
[`ProductMinusImages`](proofs/Lax342547Proofs/ProductMinusImages.lean)
proves the affine minus-image cap after exposing all plus frames; their
common annihilator has dimension at least `N-k(d+h)` for k draws.
[`ReferenceImages`](proofs/Lax342547Proofs/ReferenceImages.lean) integrates
over the actual plus-frame fibers and multiplies over components. For
two endpoints its finite cap is
`16^|E| / 2^(N t₊ + (N-2(d+h)) t₋)`, for the actual summed nominal ranks,
without requiring the original tuple columns to be independent.

[`ImageScale.reference_image_cap`](proofs/Lax342547Proofs/ImageScale.lean)
pays this fixed prefactor and dimension loss to prove exactly
`2^(-(1-ε)tN)` for every `t≥1`. The proof uses the slightly larger
prefactor `16^|E|` instead of the paper's illustrative `4^|E|`; both are
absorbed by the same type of scale choice. `exists_paper_scale` supplies
one M₀ for the actual count `d=pStar*(1+(g²+3)n)` and fixed channel size h,
valid for every positive n and independent of every tested rank and law.
All six steps in §6.1 are complete.

### 6.2 Walsh estimates, Lemma 4.6

1. **Complete.** Prove orthogonality of binary characters on a finite vector space.
2. **Complete.** Derive the `L²` operator bound for a bilinear phase from its rank.
3. **Complete.** Add affine terms and density bounds without changing the rank argument.
4. **Complete.** Formulate the conditional version used after pinning and freezing keys.

[`Walsh`](proofs/Lax342547Proofs/Walsh.lean) proves character orthogonality,
the exact transform energy identity, and Lemma 4.6(b) for real bounded
weights and subprobability masses. [`BilinearWalsh`](proofs/Lax342547Proofs/BilinearWalsh.lean)
groups weights over the fibers of a rectangular binary matrix, applies
fiberwise Cauchy–Schwarz, and uses rank-nullity to obtain the exact
`1 / sqrt(2^rank)` normalized bound. It includes the two density factors,
arbitrary separate phases, and finite conditioning records with varying
coefficient spaces and unnormalized cell masses.
[`SlotWalsh`](proofs/Lax342547Proofs/SlotWalsh.lean) identifies the actual
vector-slot pairing matrix and proves its bit rank is `N * rank C`.
A nonzero cross pattern therefore has correlation at most `1 / sqrt(2^N)`.
All three parts of Lemma 4.6 have closed checked proofs. Instantiating them
with the frame laws and pin/key quotients remains part of the later work.

**Exit condition:** exact finite estimates with explicit rank and density
parameters. Later uses should instantiate these estimates, not reproduce
informal Fourier arguments with hidden conditioning costs.

## 7. Sparse intersections and the two peelings — §4.2–4.3

### 7.1 Sparse representatives, Lemma 4.4

1. **Complete.** Count coefficient descriptions of boundedly many independent shared
   image vectors, then apply the exact-image cap and joint-density cap.
2. **Complete.** Bound the summed intersection dimensions outside an exponentially
   small exceptional set.
3. **Complete.** Transfer these bounds to the component ranks of shared tensors.
4. **Complete.** Prove the combinatorial cut argument: few unequal tag pairs force a
   strict majority of equal representatives. Normalize that value to zero
   using the cut kernel and prove uniqueness of this normalization.
5. **Complete.** Prove the support bound `4D/g` and the trace identity giving equality
   of the two `χStar` values.

[`KernelWitness`](proofs/Lax342547Proofs/KernelWitness.lean) describes a
large sum of kernel dimensions using q coefficient columns per component,
padding unused columns by zero. It proves the exact description count
`2^(|E| * 2(d+h) * q)` and the finite certificate union bound.
[`RawIntersections`](proofs/Lax342547Proofs/RawIntersections.lean) bounds
primal intersections by these relation kernels and applies the full
reference-image cap at q=2D. After paying the joint density and a coefficient
cost at most DN/4, its exceptional probability is at most `2^(-DN/4)`.

[`TensorIntersections`](proofs/Lax342547Proofs/TensorIntersections.lean)
proves rank preservation, the shared-column-space bound, and the exact
trace/self-Gram pairing. [`CutSparsity`](proofs/Lax342547Proofs/CutSparsity.lean)
counts unordered unequal tag pairs through their endpoint flags, forces a
strict majority, and proves the unique majority-zero normalization.
[`SparseRepresentatives`](proofs/Lax342547Proofs/SparseRepresentatives.lean)
applies these results to the actual allowed moment spaces and proves
the support and `χStar` assertions. Two strict majority zero sets already
intersect, so the trace argument does not need the paper's weaker combined
support estimate to find a common zero tag.

[`SparseIntersections.raw_intersections`](proofs/Lax342547Proofs/SparseIntersections.lean)
combines every conclusion of Lemma 4.4. `exists_concrete_scale` uses the
checked coordinate count to supply a single M₀ paying all its hypotheses
for every positive n, independently of the law. The paper's early constants
satisfy the required majority inequality and give support at most 16000.

### 7.2 Two peelings, Lemma 4.5

1. **Complete.** Define pins in the direct sum of the two endpoints' nominal spaces.
2. **Complete.** Specify the exact-image test that violates a desired cap and the
   refinement operation that adds it as a pin.
3. **Complete.** Prove a potential/density budget bounds the total added dimension.
4. **Complete.** Store bases, exact images, leaf weights, and the conditional leaf laws.
5. **Complete.** Prove the first leaf law has all required unpinned image caps.
6. **Complete.** Prove the second peeling after the allowed extra restrictions and pins,
   preserving old effective spaces and respecting the final budget `K`.
7. **Complete.** Track the mixed marginal bounds separately from the individual leaf
   bounds. A normalized rare leaf need not satisfy the original marginals.

[`ExactPins`](proofs/Lax342547Proofs/ExactPins.lean) stores each nominal
subspace with its prescribed linear image. It proves exact refinement
of events and identifies the rank increase with the sum of dimensions in
the old nominal quotients. Basis matrices and their exact images identify
these events with the actual raw tuples in
[`ReferencePins`](proofs/Lax342547Proofs/ReferencePins.lean).

[`LeafExtraction`](proofs/Lax342547Proofs/LeafExtraction.lean) chooses an
extension of maximal rank among those meeting the strict mass lower bound.
A violating positive-rank test would yield a larger such extension.
[`LeafPartition`](proofs/Lax342547Proofs/LeafPartition.lean) repeatedly
removes a nonempty extracted support by finite induction, leaving mass
at most delta and proving pairwise disjointness of all retained leaves.

[`PeelingBudget`](proofs/Lax342547Proofs/PeelingBudget.lean) proves the
exact comparison `(ζ-ε)u < D+ζ`, its conservative `4(D+1)/ζ` consequence,
and the density normalization cost.
[`BoundedPeeling`](proofs/Lax342547Proofs/BoundedPeeling.lean) combines
these with the normalized all-rank leaf laws.
[`RawPeeling.raw_peeling`](proofs/Lax342547Proofs/RawPeeling.lean) applies
the construction to the actual endpoint/sign observation maps. It permits
initial pins, preserves every old image, and bounds total dimension by
the initial rank plus the new budget. Empty initial pins give the first
peeling on any selected residual support, including the complement of the
Lemma 4.4 exception.

[`Conditioning`](proofs/Lax342547Proofs/Conditioning.lean) proves exact
event and density normalization formulas and reconstructs disjoint mixtures
with their actual masses. [`LeafTrimming`](proofs/Lax342547Proofs/LeafTrimming.lean)
bounds the fraction discarded after a combined restriction of mass at
least `2^(-ηN)` by `2^(-(ζ-η)N)`. On each surviving leaf it gives the
`1-2ζ` image cap and the explicit density normalization cost.
[`RestrictedLeaves`](proofs/Lax342547Proofs/RestrictedLeaves.lean) packages
these conclusions uniformly over every quotient rank and leaf in a finite
weighted family. Successive restrictions equal their combined intersection.
The separate `filtered_marginal` theorem charges a mixed-law marginal cap
only the inverse mixed retained mass; it makes no original marginal claim
for a normalized rare individual leaf.

[`MetadataPins`](proofs/Lax342547Proofs/MetadataPins.lean) counts all exact
image records as at most `|J| * 2^(uN)` and joins their pins to the old ones.
[`SplitTrimming`](proofs/Lax342547Proofs/SplitTrimming.lean) discards at most
`2^(a*n-N)` when `|J| ≤ 2^(a*n)`, hence at most `2^(-N/2)` under the explicit
scale condition `2*a*n ≤ N`. It proves the absolute starting density
`2^((D+K₁+u+5)N)` for every retained part after preceding leaf trimming.

[`SecondPeeling`](proofs/Lax342547Proofs/SecondPeeling.lean) peels each such
part while preserving all old and deliberately added pins. It proves
`K₁+u+ceil(4(D+K₁+u+6)/ζ) ≤ ceil(10(D+K₁+u+10)/ζ)` and carries the residual
bound back to the original part mass. The actual raw-law specialization is
[`raw_second_peeling`](proofs/Lax342547Proofs/RawSecondPeeling.lean).
[`MixtureRecovery`](proofs/Lax342547Proofs/MixtureRecovery.lean) proves exact
nested mass recovery and sums the per-fiber residual bounds to the same
global budget. Further restrictions use the same checked trimming theorem.
[`ProjectedPins`](proofs/Lax342547Proofs/ProjectedPins.lean) defines the
actual endpoint primal projections and effective tensor spaces, proves the
projection dimension bound, and preserves every old effective space under
pin extension. Its dimension and tensor-rank bounds are part of §9.

**Exit condition:** a finite decomposition with all mass losses, pin
dimensions, and all-rank image bounds proved. The decomposition itself
must not assume a later collision or overlap conclusion.

**Exit condition met in quantitative finite form.** The small-cost
restriction is expressed by an explicit lower mass bound `2^(-ηN)`, and
the metadata cost by an explicit count `2^(a*n)`. Later asymptotic arguments
must supply these bounds uniformly; they are not hidden in this result.

## 8. Low-rank moments and the choice of mixers — §5

### 8.1 Boolean moment algebra, Lemmas 5.1–5.3

1. **Complete.** Prove the exact span characterization of base moments: symmetry and
   `Zᵢᵢ = Z₀ᵢ`. Construct the diagonal and off-diagonal basis matrices from
   the stated sums of point moments.
2. **Complete.** Prove selector interpolation on a finite set of distinct labels using
   products of separating affine bit functions. Account for squarefree
   reduction and the degree bound.
3. **Complete.** For the low-rank label decomposition, define the truncated moment
   pairing and its increasing restrictions. Prove existence of three
   consecutive equal ranks in the required interval.
4. **Complete.** Pass to the radical quotient. Define selector multiplication on it
   and prove well-definedness, self-adjointness, commutativity, and
   idempotence separately.
5. **Complete.** Split the quotient into simultaneous binary eigenspaces. Construct
   the label blocks, prove their Boolean diagonal identities, and bound
   the sum of their ranks.
6. **Complete.** Recover higher-degree moments: a minimal discrepant monomial produces
   the identity submatrix indexed by complementary half-subsets. Prove
   its rank exceeds the rank budget.
7. **Complete.** Bound the union of sparse labels appearing in projected pin directions,
   using a basis and selector interpolation. Preserve the exact budget `B₀`.

The completed result is
[`low_rank_label_decomposition`](proofs/Lax342547Proofs/LabelDecomposition.lean).
It starts with membership in the actual point-moment span and a matrix-rank
bound, constructs every intermediate object, and assumes only `6R + 4 ≤ jStar`.
It does not take a decomposition or a flat quotient as an external hypothesis.
The reconstructed matrix is a Gram matrix on the quotient, so its rank is
bounded before applying the higher-degree uniqueness theorem. This avoids
needing to establish its moment-span membership for the reconstruction step.
The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The checked [`sparse_pin_labels`](proofs/Lax342547Proofs/SparsePins.lean)
then bounds all sparse expansions in all projected spaces, with the exact
budget `2 |E| K (R + 14)`. It constructs an independent sparse generating
family for each space and uses selector interpolation to exclude every
additional label. Both finitely supported coefficients and the paper's
finite-sum notation are covered, with degree condition
`(K + 1) * (R + 14) ≤ degree + 1` and only standard background axioms.

### 8.2 Atoms and uniform mixers, Definition 5.4 and Lemma 5.5

1. **Complete.** Define every flavor as an explicit finite parameter domain, with its
   allowed testers, free `Z` coordinates, and uniform distribution.
2. **Complete.** Express atom evaluation of the mixer form through bounded row-bit
   spaces. Prove the forward/reverse compatibility rank calculation.
   The exact compatibility condition and codimension, its observation-law
   density bound after an injective free-direction restriction, and rank
   loss of at most twice the restricted codimension are checked. The exact
   affine point-input variation under a base-block change is checked too.
   The actual atom evaluation is now a constant tester term plus an affine
   substitution into the disjoint formal quadratic. Its polar rank is the
   exact formal row dimension, and substitution loses at most twice the
   row-map codimension. The fixed row space has dimension at most
   `4J(g-1)K` and determines all evaluations before the non-Z values are fixed.
3. **Complete.** Bound the number of low-rank coefficient
   profiles and rank-deficient random row maps; union bound uniformly over
   profiles, labels, and tags. All non-Z fixings, hence all flavors, are
   covered inside each event without an additional union.
   Rectangular factorization and its probability bound are checked.
   Symmetric factorization works in characteristic two without a diagonal
   assumption. The actual cut profiles of total rank at most `K` number
   at most `(K+1)^|E| 2^(dK+K²)`, and the row-corank probability is at most
   `2^(ms)/2^(sn)`. The joint row law has domination factor `2^(2JK²)`;
   its packed matrix is proved to represent the actual formal-row map.
   Substituting the coordinate dimension and taking the finite union gives
   the explicit failure bound in `UnaryMixers.failureBound`. A proved
   threshold makes it less than one. `exists_uniform_unary` constructs
   simultaneous unary mixers and bounded row spaces for all sufficiently
   large `n`, under `p_* (g²+3) K ≤ s₀` and `k>0`, where `g=2k+1`.
4. **Complete.** For distinct labels, prove all the required nontrivial binary parities
   of ordered mixer evaluations and `E` evaluations have large rank.
   The distinct labels have independent combined free-direction columns.
   The two ordered blocks of one uniform mixer are jointly uniform. Every
   nonempty ordered parity of an independent family is uniform and obeys
   the checked low-rank probability bound. The actual `E` restriction on
   the sharp directions is the label-weighted sum of the `M_a`, and its
   free-direction restriction is zero. All three sharp-parity probability
   bounds are checked, including the alternating subblock of side `⌊n/2⌋`.
   The actual ordered point-input parity is identified with its ambient
   matrix, and its mixed coefficient matrix is the flavor restriction.
   Both always-retained blocks occur as submatrices, so the rank bounds
   hold for every flavor. Finite unions over labels and coefficients give
   explicit bounds `2^(2b+2|F|)/2^n` for indexed mixers and `2^(2b+2)/2^n`
   for the self-Gram parities when `n≥50`. The exact conclusion is
   `n ≤ 5 * rank`, with no rounding loss in the paper's `n/5` threshold.
5. **Complete.** Choose all mixer matrices simultaneously for a fixed large `n`.
   Only then quantify over unit laws and orientation-dependent effective
   spaces. The mixer choice cannot depend on those laws. Simultaneous
   unary existence is checked, including an explicit threshold independent
   of the tester family. The unary failure bound is sharpened to `C/2^n`.
   Adding the indexed binary failure bound gives a sum below one above
   `UniformMixers.threshold`; the sharp matrices are chosen next.
   The checked paper parameters are `s₀=40(K+1)p_*(g²+5)` and
   `J=101(s₀+K²+1)`. This closes the mixer-specific parameter obligations;
   the remainder of Appendix A still belongs to §17.

The unary endpoint is
[`exists_uniform_unary`](proofs/Lax342547Proofs/UnaryMixers.lean).
It quantifies over all nonzero actual cut profiles of total rank at most
`K`, then tags and labels, then chooses the bounded row space, then
quantifies over allowed base-coordinate fixings. It proves both the
`2(J-s₀)` polar-rank bound and dependence only on those row bits. Its
closure uses only `propext`, `Classical.choice`, and `Quot.sound`.

**Exit condition:** a proved existence theorem for the mixers with every
consumer-visible property explicit. This is one of the main algebraic
checkpoints; its rank estimates must be fully expanded in Lean.

**Exit condition met.**
[`UniformMixers.exists_paper_mixers`](proofs/Lax342547Proofs/UniformMixers.lean)
supplies both parts of Lemma 5.5 for every sufficiently large `n`, before
any unit law is chosen. The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for this endpoint.

## 9. Scalar recipes and full gradient realization — §6

**Inputs:** the concrete model, pin metadata, low-rank moment decomposition,
sparse-label bounds, and mixers.

1. Define effective spaces, small tables, admissibility, injection flags,
   and the private/protected channel decomposition.
   **Complete.** These spaces and flags are defined. Effective dimension
   and total-rank bounds, table dimension bounds, protected projection
   bounds, private complements, and pin-extension monotonicity are checked.
   The table-derived contraction is well defined on effective profiles,
   independent of its chosen linear extensions, and agrees with actual
   channel contractions whenever the full cross forms extend the table.
2. Define witness lists and all scalar recipe equations. Preserve the
   allowed lengths `1,…,7` and freshness of labels across both incident lists.
   **Complete.** Actual point atoms and their numerical tester records
   are defined. The full paired-list structure records matched tags and
   diagonal bits, label freshness, lengths, role parity, both effective-space
   equations, and both coupled endpoint equations. Each endpoint uses at
   most fourteen rays; diagonal sums and matched-key tensor sharing are proved.
3. Prove Lemma 6.2: the table restrictions separate into two orientation
   filters; fresh key directions are independent modulo the stored spaces;
   the binary prescriptions are consistent exactly when the scalar
   compatibility equations hold.
   **Core assertions checked.** Unary separation is specialized to actual
   frame observations. Fresh-key independence covers all components and
   signs, with one exclusion per endpoint. The role and coupled equations
   construct a symmetric matrix and indexed L/R prescriptions that give
   the concrete atom-gradient identities. Table counts and padded nominal
   coefficient counts are checked. Integration with the full paired-list
   recipe is checked at all four endpoints. The complete numerical metadata
   format remains.
4. Prove the linearized realization problem by annihilator duality.
   A putative obstruction has bounded component rank; use the label
   decomposition and injection flags to reduce it to atom and effective
   space equations already included in the recipes.
   **In progress.** The target residual is proved to vanish on the effective
   profile space plus the span of every selected endpoint atom. The remaining
   obligation is to put every annihilator obstruction in that space. The
   pure-response system on actual pairs of cut profiles is now defined;
   its component rank bound `2K+28` and the resulting label decompositions
   are checked. Selected affine-ray moment blocks reduce to scalar point
   moments, and sparse pin exclusions cover arbitrary base coefficients.
   The quotient extractors now isolate the actual selected tensor blocks.
   Triangle interpolation gives one scalar for each selected witness on
   its entire tag star. Subtracting these actual atoms preserves pure
   annihilation and gives a reconstruction on unselected labels with the
   same support and sum-of-block-ranks budgets. The full response, including
   both allowed derivative families, now kills every selected atom and is
   preserved by subtraction. Both reciprocal unselected contractions lie
   in their actual primal pins. Rank-one derivative tests and the actual
   row and column injection flags force both contractions to zero.
   Conversion to effective profiles and the final duality argument remain.
5. Construct bounded-rank derivative corrections. Prove the baseline
   rank `3K+28` and residual rank `14K+140`, rather than declaring them
   as opaque bounds.
   **In progress.** The actual baseline cross forms are constructed, extend
   the prescribed tables, and preserve every frozen pin and fresh selected
   key. Their channel ranks are at most `3K+28` in both reciprocal endpoint
   roles. Controlled derivative corrections and the residual bound remain.
6. Prove the block compression maps preserve allowed point moments and
   therefore preserve the cut-profile domain.
7. Bound the pure correction rank by `30r₀ + 28J|E| + Dquo`.
8. Factor the correction through the remaining private channel pairing.
   Verify orthogonality to the baseline and earlier corrections, and
   simultaneous consistency in the two endpoint roles.
9. Conclude the gradient identities on **every vector of the cut space**,
   not just on a sampled family of atoms. Count the scalar constraints
   needed to test them later.

**Exit condition:** Theorem 6.3 with no existential field that simply
assumes solvability of the gradient system. The private-channel capacity
must follow from the stated parameter inequality.

[`EffectiveBounds`](proofs/Lax342547Proofs/EffectiveBounds.lean) proves
`dim C_i ≤ K²` and total component rank at most K by embedding in the
component tensor spaces. [`TableSpaces`](proofs/Lax342547Proofs/TableSpaces.lean)
and [`SmallTables`](proofs/Lax342547Proofs/SmallTables.lean) use the actual
nominal endpoint blocks. The injection quotients use the protected channel
of the pinned input's sign, even though the table evaluates against the
opposite-sign channel. `raw_admissible_iff_filters` uses fixed stored pin
images to separate both cross orientations.

[`TensorContractions`](proofs/Lax342547Proofs/TensorContractions.lean)
constructs the linear dot-product contraction on the tensor span and proves
that all ambient extensions give the same value. This gives the effective
table contraction in [`TableContractions`](proofs/Lax342547Proofs/TableContractions.lean).
[`RawContractions`](proofs/Lax342547Proofs/RawContractions.lean) identifies
its ambient formula with the actual raw-frame trace contraction.
[`PairedWitnesses`](proofs/Lax342547Proofs/PairedWitnesses.lean) supplies the
full scalar-recipe definition, fourteen-ray bounds, diagonal identities,
and sharing of the two witness tensors under positionwise matched keys.

[`FreshKeys.fresh_keys`](proofs/Lax342547Proofs/FreshKeys.lean) projects any
purported dependence onto each endpoint. The sparse exclusion and the
nonzero constant coordinate force all coefficients to vanish.
[`TableCounts`](proofs/Lax342547Proofs/TableCounts.lean) bounds the number
of tables by `2^(2|E|(2K+2h)^2)` and the number of padded nominal coefficient
records by `2^(4|E|K(dim B+h))`; every permitted pin space has such a record.

[`SymmetricPrescriptions`](proofs/Lax342547Proofs/SymmetricPrescriptions.lean)
constructs the compatible diagonal and off-diagonal blocks explicitly.
[`RecipeRows`](proofs/Lax342547Proofs/RecipeRows.lean) derives their cross
compatibility from the two role equations and the opposite coupled
equation. [`BinaryPrescriptions`](proofs/Lax342547Proofs/BinaryPrescriptions.lean)
uses one allowed ordered product per distinct pair.
[`WitnessAtoms`](proofs/Lax342547Proofs/WitnessAtoms.lean) and
[`AtomProducts`](proofs/Lax342547Proofs/AtomProducts.lean) identify the
numerical tester part and actual ordered mixer evaluations.
[`ConcreteRecipes.prescribe`](proofs/Lax342547Proofs/ConcreteRecipes.lean)
chooses the bits before any actual atoms or mixer matrices, then proves
the requested gradient identities for every realization of those tests.
It assumes neither occurrence nor independence of the evaluations.
[`PairedRecipes`](proofs/Lax342547Proofs/PairedRecipes.lean) applies those
prescriptions to both lists at both endpoints. [`KeySpans`](proofs/Lax342547Proofs/KeySpans.lean)
and [`PairedKeys`](proofs/Lax342547Proofs/PairedKeys.lean) prove disjointness
of the actual incident key spans from the tables and their dimension bound 28.

[`FrozenBaselines`](proofs/Lax342547Proofs/FrozenBaselines.lean) constructs
splittings and a table-compatible frozen extension. [`PrimalRetractions`](proofs/Lax342547Proofs/PrimalRetractions.lean)
and [`BaselineRank`](proofs/Lax342547Proofs/BaselineRank.lean) choose primal-preserving
retractions and prove reciprocal rank bounds for the same extension.
[`NominalBaselines`](proofs/Lax342547Proofs/NominalBaselines.lean) and
[`RawBaselines`](proofs/Lax342547Proofs/RawBaselines.lean) specialize these
bounds to the actual tables and selected key spans, giving `3K+28`.
[`FrozenValues`](proofs/Lax342547Proofs/FrozenValues.lean) evaluates the
selected atoms; [`RecipeResiduals`](proofs/Lax342547Proofs/RecipeResiduals.lean)
proves that the target residual vanishes on effective profiles and all
selected atoms. The whole-space annihilator argument and derivative
corrections are still open.

### 9.1 Detailed annihilator reduction

This expands §9.4 into the next mathematical obligations. Completing the
individual matrix lemmas does not close the coupled obstruction argument.

| Stage | Exact obligation | Advancement |
| --- | --- | --- |
| Frozen quotients | Quotient by actual pins, incident selected keys, and private channel directions; prove each primal projection is in the corresponding pin-plus-key space | Checked in `BarredSpaces` |
| Pure response | Define independent component bilinear responses on these quotients as functionals on a pair of actual cut profiles | Checked in `PureObstructions` |
| Individual rank | Separate each endpoint and component; prove rank at most `2K+28` from the two kernel dimensions | Checked in `QuotientRank`, `TensorAnnihilators`, and `PairedAnnihilators` |
| Label decomposition | Apply Lemma 5.2 to every actual component, retaining the label count, Boolean identities, and sum-of-block-ranks bound | Checked in `PureObstructions.component_labels` |
| Strong sparse exclusion | Choose one exclusion covering arbitrary base-vector coefficients in every short projected pin expansion, including expansions with other excluded labels | Checked in `PinLabelExclusions`; it implies the earlier fresh-key hypotheses |
| Isolate selected blocks | Extract the fresh coefficient through the pin-plus-key quotient and apply it to each component label summand | Checked in `TensorBlocks` and `SelectedBlocks`, using the actual witness lists |
| Scalar selected moment | Prove a Boolean base moment killed modulo that affine ray in both factors equals a scalar point moment | Checked in `SelectedMoments` and `TensorAnnihilators.selected_block` |
| Cut consistency | Separate the triangle relations label by label and prove the selected scalar is equal on every component of its tag star | Checked in `LabelRelations` and `SelectedScalars.selected_decomposition` |
| Subtract selected atoms | Subtract those scalar multiples as actual cut profiles, preserving response annihilation and the component rank and support budgets | Full pure and derivative annihilation, selected subtraction, and bounded unselected reconstruction checked in `DerivativeResponses.unselected_obstruction` |
| Derivative response | Define all allowed derivative maps into the protected-channel orthogonal spaces; prove their frozen-entry and reciprocal-role compatibility | Allowed bilinear changes checked in `ChannelChanges`; the full pure-plus-derivative functional system on actual profile pairs is assembled in `DerivativeResponses` |
| Eliminate residual keys | For an unselected residual profile, use the strong exclusion and protected/private complement to remove every selected key and channel term in a pure contraction | Both signs checked using `PrimalContractions.unselected_pin_contraction_mode` and transposition of the paired quotient tests in `DerivativeContractions` |
| Use table injection | Test rank-one derivative maps; use both injection flags to force each residual contraction to vanish | Actual rank-one tests and both zero-contraction conclusions checked in `DerivativeResponses.plus_contraction_zero` and `minus_contraction_zero` |
| Effective residual | Convert vanishing contractions into membership in the projected pin tensor products, then remove their remaining key directions | Open |
| Linear solvability | Combine effective and selected-atom residual vanishing with the proved obstruction reduction and finite-dimensional annihilator duality | Open |

For the selected-block step, let L be the union of a component's moment
labels and the selected key labels. Define `E_L(c)` as the sum of
`labelTensor s (c s)`. At a fresh selected label s, the strong pin cover
forces the s coefficient of any pin in this sum to vanish. Modulo the
selected key span it can therefore change only along that label's
incident affine key ray. Factor the coefficient projection, followed by
the quotient by that ray, through `E_L` and the pin-plus-key quotient;
then extend it linearly to the ambient quotient. These two extractors
are checked in `QuotientExtractors`. `TensorBlocks.block_contraction`
proves that contraction commutes with a base block's tensor lift.
Pulling back arbitrary base quotient bilinear forms therefore isolates
the selected base moment block. `SelectedBlocks.selected_obstruction`
applies this to the actual lists, pins, and obstruction components.
For a nonincident selected atom the ray is zero, so the entire block must
vanish. For an incident atom, `TensorAnnihilators.selected_block` supplies
its scalar point-moment form.

For triangle consistency, use the union of the three component label
sets, whose size is at most `3R_*`. Selector interpolation separates the
actual cut triangle identity at each label. The selected label is
supported on its tag star; evaluate the resulting matrix identity at
its two constant base coordinates to compare the scalar coefficients.
The selected point has constant coordinate one. These steps are checked
in `LabelRelations` and `SelectedScalars`. The endpoint
`SelectedScalars.selected_decomposition` chooses the component blocks
and the common scalar for every selected witness directly from an actual
pure obstruction. `ResidualLabels.unselected_obstruction` subtracts the
resulting scalar atoms in the actual cut-profile space and deletes their
labels from the reconstruction. Every surviving block keeps its Boolean
moment identities; the support and sum-of-block-ranks bounds stay at
`2K+28`. Pure annihilation is preserved, so the existing component-rank
theorem also applies to the remainder. Exact nonincrease relative to each
original component's rank is not asserted by this endpoint.

`SparseKeyCoefficients.coefficients_zero` extracts every fresh key
coefficient from a short key combination differing from an unselected
sparse vector by a projected pin. `BarredElimination.sparse_barred`
applies it to both endpoint projections of an actual barred decomposition.
All key projections vanish. Protected/private channel complementarity
then forces the private vector to vanish, leaving a pin vector.
`PrimalContractions.endpoint_vector` detects nominal contraction membership
by testing products of quotient functionals and using double annihilation.
`sparse_contraction` retains the selector row factors in a matrix contraction.
`unselected_pin_contraction` combines these with the actual barred elimination:
an individual minus functional killing its projected pin and key directions
contracts the sparse residual into the actual plus pinned primal space.

`ChannelChanges` defines the allowed quotient maps into perpendicular
protected-channel spaces and their bilinear implementation. It proves
frozen-entry preservation, vanishing on opposite primal inputs, and exact
reading of each output coordinate on a channel basis vector. Coordinate
duality detects protected-space membership from orthogonal tests. The
actual table's first and second injection flags then give row and column
zero-vector criteria for pinned primal inputs. The scalar pairing tests
are now derived from the full derivative response below.

`DerivativeResponses` assembles the two allowed derivative families with
the independent pure bilinear family, on the actual pair of cut profiles.
Every selected atom kills this full response; selected subtraction preserves
it, and `unselected_obstruction` retains the original support, Boolean moment,
and sum-of-block-ranks budgets. Each component can be tested independently.
An individual functional killing its projected pin and keys descends through
the actual barred quotient after being extended by zero on the other primal
endpoint and channels. Multiplying it by an allowed perpendicular channel
vector gives a rank-one derivative test. The checked scalar identity reads
the baseline evaluation of the residual contraction. Pin membership and the
actual row injection flag force the plus contraction to zero. Transposing
the paired tensor test, using the minus protected/private complement, and
testing the reciprocal derivative gives the minus zero-contraction result.
No symmetry assumption on an arbitrary residual matrix is needed.

The next obligations are:

1. Convert the two vanishing contraction statements into row and column
   membership in the projected pin-plus-key spaces. Prove the corresponding
   matrix is in their tensor product, then remove keys using the unselected
   sparse row and column reconstructions to obtain actual effective profiles.
2. Package the response families as a linear map from their finite-dimensional
   parameter space to the dual of the actual profile-pair space. Prove
   linearity in these parameters explicitly. Combine the effective remainder
   and selected atoms with target residual vanishing, and use annihilator
   duality to construct an unrestricted linearized solution.
3. Prove the bounded-rank derivative corrections, compression, pure correction
   rank bound, and private-channel factorization required by Theorem 6.3.

The checked rank and selected-moment steps are independent of the private
channel dimension. The derivative and injection steps use the actual table
maps. The remaining effective-space and duality steps must retain these definitions;
an assumed obstruction-space inclusion would leave the argument unproved.

## 10. Accepted queries imply four holes — §7

1. Define global key slots and their constrained reference distribution.
   Prove the size/density bounds for every query shape.
2. Define accepted queries and their unnormalized key densities.
3. For fixed leaves, pins, parameters, and keys, identify the numerical
   records and the two separate orientation cells. Opposite-parameter
   dependence must not become opposite-orientation dependence.
4. Bound the overlap discarded by pruning cells below the given threshold.
5. On retained cells, combine the fresh-image cap with the Walsh bounds.
6. Expand the finite system of scalar constraints in binary characters.
   Separate nonzero quotient tensors from the zero-quotient characters,
   for which compatibility must be checked exactly.
7. Apply gradient realization to accepted equal keys and build the four
   actual hole witnesses.
8. Prove Proposition 7.1 with its exact exponential loss, including the
   maximum slot count `kMax = 56(g-1)`.

**Exit condition:** an explicit inequality converting successful-query
overlap into four-hole probability. It must handle the overlap scales
used by both final branches.

## 11. Phase alternatives and status preparation — §§8–9

### 11.1 Phase alternatives, Theorem 8.2 and Lemmas 8.3–8.5

1. Define marked units, their tensors `Δ`, and componentwise covers.
2. Prove the rank-deficit inequality for sums after quotienting exposed
   column and row spaces.
3. Prove the random-permutation span-increment argument and the dyadic
   scale selection. Derive the no-cover rank-growth probability bound.
4. Use high moments and channel randomness to control each nontrivial
   phase. Retain all density and moment-order costs.
5. In the cover case, prove the singleton phase estimates and the second
   concentration step yielding either full cancellation or a tiny cover.
6. Prove injection on accepting pairs with the stated finite-family
   count. Its exponential coefficient must not acquire an unbudgeted
   dependence on the channel dimension.
7. Prove the tiny-cover consequences, including the inverse-polynomial
   compatibility probability. A fixed positive lower bound is not claimed
   in this alternative.

### 11.2 Common predictions, Proposition 9.2 and Lemmas 9.3–9.5

1. Define a common prediction with one global key function per endpoint,
   uniform error over every retained unit and every allowed unary type,
   and bounded label exceptions. The functions cannot vary by orientation.
2. Define prediction classes using asymptotic agreement on every tag/bit
   space, modulo a **single common multiple** of the diagonal bit.
3. Prove the Boolean polynomial nonvanishing estimate. Use it to turn
   vanishing prediction errors into exact identities on all of `X`.
4. Prove affine-slice comparison with the actual conditional frame law.
5. Prove the zero-`Δ` tester-rank argument forces equal coefficients.
6. Combine these with the phase alternative and the second peeling.
   Produce the three separate preparation alternatives, keeping old
   marks, excluded labels, exact pins, and numerical formats.
7. Verify the positive-mass table alternatives and the rare alternative's
   `c₂ N⁻⁴` leaf-pair mass plus fixed positive masses of its two filters.

**Exit condition:** preparation is stated along a bad sequence of laws,
with justified subsequence choices and relative mass `2^(-o(N))`.
No later scalar-solvability conclusion is used to prove preparation.

## 12. Histogram control and positivity — §10

The order within this section matters: its opening histogram-control
statement is proved using estimates developed later in the section.

1. Prove Gram normalization for key tuples and comparison of two bounded
   batches (Lemmas 10.2–10.3), including repeated-label patterns.
2. Prove product reference tests for fixed bounded unary tests (10.4).
3. Prove the many-query/prescribed-cell estimate (10.5). Keep the query
   count and the leaf density penalty explicit before optimizing them.
4. Deduce uniform small-set control and own-leaf histogram nets (10.1).
   The family must cover **all orientation filters** with bounded flags,
   and its size bound must be independent of `n`.
5. Prove typicality of fixed common input-and-key tests under the mixed
   marginal assumptions (10.7). Do not strengthen this to arbitrary
   tests selected after seeing an orientation.
6. Prove binary mixing with arbitrary bounded unary input weights and
   prescribed binary/Gram conditions (10.9).
7. Prove quadratic bias on affine subspaces from polar rank (10.10).
8. Prove unary positivity (10.11): use the free-`Z` change-of-basis action,
   bounded row-bit spaces, and the martingale/orthogonality argument;
   union bound over the allowed low-rank profiles.
9. Fourier-invert the basis bits. Obtain a positive assignment fraction
   independent of the chosen positive-measure global key cell, while
   allowing the onset to depend on that cell's measure.

**Exit condition:** separate the reference law, each normalized leaf, and
the mixed law in all statements. Uniformity over cells means the precise
quantifier order in the paper, not a simultaneous assertion about all
cells at each orientation.

## 13. Weak product comparison — §11

1. Define the finite family of crossing Gram twists and the corresponding
   cut norm.
2. Prove the twisted regularity lemma (11.2) by an energy-increment
   refinement. Bound the number of refinements and the expansion size.
3. Prove the terminal remainder lemma (11.3): fourfold Cauchy–Schwarz
   removes arbitrary unary orientation weights; typicality replaces the
   fixed test by its reference average; frame/Walsh estimates bound the
   surviving Fourier terms.
4. Treat terms without a cross pattern by the twisted cut norm. Do not
   discard those terms as though all nontrivial characters mixed.
5. Recursively split the groups and choose each error budget only after
   the previous expansion's complexity has been fixed.
6. On the constrained key support, remove the twists and obtain Theorem
   11.1 with bounded sums of products of global unary key functions.
7. Prove factorized integration (11.4) with exactly the permitted unary
   filters and binary prescriptions.

**Exit condition:** the comparison theorem applies to the actual queries
used downstream. It must not accidentally allow arbitrary joint nominal
input filters, which the paper does not establish.

## 14. A common limit with conditional laws — §12

This is a major analysis checkpoint, not a routine compactness invocation.

1. Specify finite numerical options (12.1), and prove that there are
   boundedly many formats independent of `n`.
2. Prove the global projection lemma (12.3): truncate densities, use
   own-leaf nets, form their covariance operators, and capture their
   large eigenspaces in a finite common partition. Control the remainder
   by trace/Hilbert–Schmidt bounds and independence of the leaf laws.
3. Prove that the same partition bound permits adaptive choices of filters
   after both leaves are known. This needs the sum over all net members;
   it does not follow merely from a bound for one fixed filter.
4. Enumerate countably many common unary/tuple tests, closing the lists
   under the projection and product-approximation requirements.
5. Construct the compact spaces of consistent cylinder masses and take
   a common subsequence for reference laws, orientation arrays,
   approximation coefficients, and successful-query measures.
6. Store the two conditional orientation laws as coordinates of the
   leaf-pair record before taking limits. Prove product sampling of
   those stored laws is continuous on the required tests. This avoids
   an unjustified interchange of disintegration and weak convergence.
7. Use cylinder consistency to construct countably additive limiting
   measures. Prove domination, jointly measurable unary densities,
   positivity, and exact limiting predictions (12.4).
8. Prove vanishing-overlap implies zero product of limiting densities
   (12.5). Establish this first for truncations using the common
   projections, then remove truncations by uniform integrability.
9. Identify the entire successful-query density from the unary status
   densities using §11 (12.6).
10. Combine these to obtain the limiting overlap obstruction (12.7).

**Exit condition:** all measurability, compactness, subsequence, and
uniform-integrability obligations are actual theorems. Check available
mathlib APIs for the required measure compactness and measurable density
versions before committing to a specific representation of the limit.

## 15. Solve the scalar system and obtain positive overlap — §13

1. Define available generators with their tag, label, flavor, and positive
   overlap certificates (13.1). Keep the full certificate when taking spans.
2. Prove the finite linear-algebra duality statement (13.2), including
   surjectivity onto the base coordinates and kernel dimension at most two.
3. In the no-prediction case, turn a positive mass of dual relations into
   deterministic common offsets. Prove uniqueness across overlapping
   label exclusions and the finite bound on offset possibilities.
4. Transfer these limiting offsets back to actual global key functions
   using cylinder approximation and strict error events. This proves
   the contradiction with no prediction (13.3).
5. In the predicted case, compare all available role/basis assignments
   to identify the dual coefficients. Classify the possible two-endpoint
   support patterns and use the prepared phase equations to kill every
   obstruction (13.4).
6. Combine with the table mass bounds to obtain scalar solvability on
   positive mass, robust under the allowed exclusions (13.5).
7. Prove stable fresh lists (13.6): at most eight span-dimension drops;
   stabilize under further bounded deletions; show kernel words of
   length at most three span the kernel; correct a singleton lift with
   at most two such words. This gives `1+3+3=7` with fresh labels.
8. Refine aggregated tester statuses, assign the consistent binary bits,
   and obtain a usable numerical option. Its positive generator overlaps
   contradict the zero-product conclusion of §12, proving 13.7.

**Exit condition:** positive expected unnormalized overlap for each
positive-mass preparation alternative. This does not settle the rare
preparation alternative.

## 16. Preserve inverse-polynomial overlap — §14.1–14.3

1. Prove the uniform large-set hit estimate (14.1), including a bad-event
   tail smaller than every inverse polynomial. A generic `o(1)` error
   is insufficient here.
2. Derive fixed-size superlevel-set families from all-filter nets (14.3).
   Construct each family using one leaf alone, before seeing the other.
3. In the exact-prediction alternative, choose one atom per cross edge
   and verify all scalar equations from the pinned compatible table.
4. Show the filtered second-side successful density has fixed positive
   mass outside an exponentially small set of leaves.
5. Choose a superlevel-set family member for that density. Its dependence
   on the other leaf is only the selection of a member of an already
   fixed bounded family.
6. Use independence of the original leaves for the first-side union bound,
   then Markov to discard only `o(N⁻⁴)` leaf-pair mass.
7. On each remaining compatible pair, combine the hit lower bound with
   the superlevel lower bound and small-set control.
8. Integrate over the remaining `Ω(N⁻⁴)` compatible pairs, proving
   Proposition 14.4 with an explicit constant independent of `n`.

**Exit condition:** the `N⁻⁴` mass is preserved before conditioning on
compatibility. The positive-mass compactness argument is not used to
replace this quantitative proof.

## 17. Choose parameters and close the theorem — Appendix A and §14.4

The parameter ledger is developed alongside the earlier stages and its
existence theorem is closed here. The order is:

\[
(C_0,g,D,M,k_{\max},\zeta,K_1)
\to(r,L_0,d_0,u_0,K,\text{early tolerances},p_0)
\to(R_*,j_*,B_0,B_*,b,p_*,A,s_0,J)
\to(r_0,h)\to M_0\to n.
\]

1. Convert every requirement used above into an explicit predicate in the
   ledger. Prove that it depends only on parameters chosen earlier.
2. Prove existence of sufficiently large selector/mixer constants and
   sufficiently small `p₀`.
3. Prove the channel demands can all be met with `h = 1000r₀`, including
   the private-channel rank margin, moment estimates, accepting-family
   estimates, and tester-rank margin.
4. Choose `M₀` to pay every fixed `O(n)` information cost. Then combine
   the finitely many eventual conditions on `n`.
5. Negate the desired uniform supersaturation statement and select an
   increasing bad sequence of `n` and admissible laws. Mixers remain those
   already fixed before the laws.
6. Apply preparation. Use §15 for positive-mass alternatives and §16 for
   the inverse-polynomial alternative. Both yield overlap `2^(-o(N))`.
7. Apply the collision theorem and restore the retained-law mass. When
   two independent units are drawn, a restriction can cost the square
   of its retained mass; include that factor explicitly.
8. Check the final exponent using `56(g-1)` slots and all fixed slacks.
   Contradict the claimed failure of the `2^(-100gN)` lower bound.
9. Apply the finite graph transfer. Prove `m = 2^(1000gM₀n)` is unbounded
   and choose `n` large enough for any requested order lower bound.
10. Replace the current use of the construction concept axiom in both
    counterexample corollaries with the proved construction, and run the
    closing checks in §1 of this plan.

## 18. Execution order and checkpoints

The suggested proof order is:

1. Finish the concrete §2 model and the common probability interfaces.
2. Complete the finite §3 transfer, while establishing basic frame and
   Walsh estimates. This gives a precise, tested interface for Theorem 3.1.
3. Close sparse intersections, peeling, moment decomposition, and mixers.
4. Close gradient realization and the collision theorem.
5. Develop the two branches of preparation and the histogram estimates.
6. Close weak product comparison, the common limit, and scalar solvability.
7. Close the quantitative rare-overlap argument.
8. Finish parameter existence, uniform supersaturation, graph existence,
   and the final counterexample statements.

The main uncertain checkpoints are the low-rank moment decomposition,
uniform mixer construction, gradient realization, phase/peeling bounds,
all-filter histogram control, adaptive common projections, and the rare
overlap tail. They need expanded proofs; merely transcribing their
statements will not reduce the main gap.

For each completed intermediate theorem, record its paper label, exact
Lean declaration, hypotheses, quantitative losses, and axiom closure.
If an attempted statement fails, record the specific obstruction and
check the paper's argument before altering the interface. Do not silently
weaken a theorem until its downstream application becomes impossible.

This plan may need refinement as those checkpoints are formalized. It
does not assume that every argument in the paper will translate without
additional mathematics.
