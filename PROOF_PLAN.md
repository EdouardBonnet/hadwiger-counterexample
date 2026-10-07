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
| Independence of representative sums | New checked generic proof; concrete testers still need instantiation |
| Symmetry and diagonal of the gradient form | New checked generic proof; concrete mixers still need instantiation |
| Matrix frame existence, tensor embedding, and finite raw-space count | New checked proofs; uniform law defined |
| Base-moment span and selector interpolation, Lemma 5.1 | Complete checked proofs |
| Low-rank label decomposition, Lemma 5.2 | Complete checked proof, including the sum-of-ranks bound |
| Uniform sparse pin label budget, Lemma 5.3 | Complete checked proof, over all sparse vectors in all projected spaces |
| Entire concrete model, with the paper's testers and mixers | Not assembled |
| Entropy/containers and the probabilistic construction | Not proved |
| Theorem 1.1 | Open |
| Counterexample corollaries | Checked only conditional on Theorem 1.1 |

Numbered steps can measure checklist progress, but they are not equal units
of difficulty or time. The October 7 moment-algebra work completed all seven
steps in §8.1; substantial parts of the construction remain open.

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

1. Specialize `MomentSpace.point` to the squarefree selector evaluations.
   Prove the coefficient count
   `pStar = ∑ j ≤ jStar, b.choose j` and the base dimension.
2. Instantiate `TagGeometry.allowedBase` for the paper's `O,S,#,Z`
   coordinates. The majority-intersection and cut-kernel proofs are now
   available; connect them to this specialization.
3. Define each ordinary tester and the shared tester by selecting the
   indicated ordered matrix entries and summing the `r₀` pairs. Prove
   their evaluation formulas on point moments.
4. Show ordinary testers vanish on `WStar`. Apply the representative-sum
   invariance theorem to construct genuine linear functionals `a_t`,
   `a`, and `b_t` on the cut space, using quotient/range descent.
   Keep `χStar` a function of a **representation**, as in the paper.
5. Define `T⁰`, `B¹`, `T¹`, and `T`. Instantiate `GradientForm` to obtain
   symmetry and `T x x = a x`. Record the ordered components in `B¹`.
6. Define the ordered tester matrix and `E#`, using selector degree one.
   Prove `⟨E,w⟩ = η(w)` for every `w ∈ W`, and prove invariance under
   every invertible change of the free `Z` coordinates.
7. Assemble the matrix frames, finite raw space, and uniform law.
   Use the explicit frame construction to prove nonemptiness for
   `N ≥ 2(d+h)`. Prove the product law across components and the bound
   `|Ω| ≤ 2^(2|E|N(d+h))`.
8. Restrict the checked tensor embedding to the cut space and produce
   the actual `HoleData`. Instantiate the checked hole and sampling
   results to obtain `indepNum ≤ 2` for every sample.

**Exit condition:** a concrete `Model` can be constructed from arbitrary
parameter values satisfying the elementary dimension conditions and
arbitrary mixer matrices. The model's independence bound is a closed
proof. No connected-matching claim is attached to arbitrary mixers.

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

1. Prove the paired-frame orbit theorem by extending an isomorphism on
   the intersection with the pairing kernel, then matching complementary
   lifts. Verify that the resulting map and inverse transpose satisfy
   both frame identities.
2. Prove the Gram probability bounds by exposing the plus vectors and
   then the minus columns. Bound rank failure by a union over nonzero
   coefficient vectors.
3. Identify the marginal and conditional laws of primal and channel
   frames, using orbit uniformity and equal completion counts.
4. Prove conditional independence of the two channel draws given `P,Q`.
   It is a different claim from independence of all four frame maps.
5. Prove the reference exact-image cap for a tuple with total nominal
   rank `t`, measured in the direct sum of both endpoints and both signs.
   Keep the bound uniform for every possible `t`, including `t = O(n)`.
6. Expose the fixed conditioning factors and the loss of `2(d+h)`
   dimensions. Pay them using `M₀` and a sufficiently large `n`.

### 6.2 Walsh estimates, Lemma 4.6

1. Prove orthogonality of binary characters on a finite vector space.
2. Derive the `L²` operator bound for a bilinear phase from its rank.
3. Add affine terms and density bounds without changing the rank argument.
4. Formulate the conditional version used after pinning and freezing keys.

**Exit condition:** exact finite estimates with explicit rank and density
parameters. Later uses should instantiate these estimates, not reproduce
informal Fourier arguments with hidden conditioning costs.

## 7. Sparse intersections and the two peelings — §4.2–4.3

### 7.1 Sparse representatives, Lemma 4.4

1. Count coefficient descriptions of boundedly many independent shared
   image vectors, then apply the exact-image cap and joint-density cap.
2. Bound the summed intersection dimensions outside an exponentially
   small exceptional set.
3. Transfer these bounds to the component ranks of shared tensors.
4. Prove the combinatorial cut argument: few unequal tag pairs force a
   strict majority of equal representatives. Normalize that value to zero
   using the cut kernel and prove uniqueness of this normalization.
5. Prove the support bound `4D/g` and the trace identity giving equality
   of the two `χStar` values.

### 7.2 Two peelings, Lemma 4.5

1. Define pins in the direct sum of the two endpoints' nominal spaces.
2. Specify the exact-image test that violates a desired cap and the
   refinement operation that adds it as a pin.
3. Prove a potential/density budget bounds the total added dimension.
4. Store bases, exact images, leaf weights, and the conditional leaf laws.
5. Prove the first leaf law has all required unpinned image caps.
6. Prove the second peeling after the allowed extra restrictions and pins,
   preserving old effective spaces and respecting the final budget `K`.
7. Track the mixed marginal bounds separately from the individual leaf
   bounds. A normalized rare leaf need not satisfy the original marginals.

**Exit condition:** a finite decomposition with all mass losses, pin
dimensions, and all-rank image bounds proved. The decomposition itself
must not assume a later collision or overlap conclusion.

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

1. Define every flavor as an explicit finite parameter domain, with its
   allowed testers, free `Z` coordinates, and uniform distribution.
2. Express atom evaluation of the mixer form through bounded row-bit
   spaces. Prove the forward/reverse compatibility rank calculation.
3. Bound the number of low-rank coefficient profiles and rank-deficient
   random row maps; union bound uniformly over profiles, labels, tags,
   and flavors.
4. For distinct labels, prove all the required nontrivial binary parities
   of ordered mixer evaluations and `E` evaluations have large rank.
5. Choose all mixer matrices simultaneously for a fixed large `n`.
   Only then quantify over unit laws and orientation-dependent effective
   spaces. The mixer choice cannot depend on those laws.

**Exit condition:** a proved existence theorem for the mixers with every
consumer-visible property explicit. This is one of the main algebraic
checkpoints; its rank estimates must be fully expanded in Lean.

## 9. Scalar recipes and full gradient realization — §6

**Inputs:** the concrete model, pin metadata, low-rank moment decomposition,
sparse-label bounds, and mixers.

1. Define effective spaces, small tables, admissibility, injection flags,
   and the private/protected channel decomposition.
2. Define witness lists and all scalar recipe equations. Preserve the
   allowed lengths `1,…,7` and freshness of labels across both incident lists.
3. Prove Lemma 6.2: the table restrictions separate into two orientation
   filters; fresh key directions are independent modulo the stored spaces;
   the binary prescriptions are consistent exactly when the scalar
   compatibility equations hold.
4. Prove the linearized realization problem by annihilator duality.
   A putative obstruction has bounded component rank; use the label
   decomposition and injection flags to reduce it to atom and effective
   space equations already included in the recipes.
5. Construct bounded-rank derivative corrections. Prove the baseline
   rank `3K+28` and residual rank `14K+140`, rather than declaring them
   as opaque bounds.
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
