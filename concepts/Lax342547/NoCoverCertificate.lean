import Lax342547.ProjectedCounts
import Lax342547.ExposedSums
import Lax342547.FilterOccurrences
import Lax342547.CoverCounts

/-!
---
title: A low rank sum supplies an actual adaptive cover
type: lemma
---
The complete deterministic greedy exposure proof turns a low rank sum into disjoint exposed and covered index sets, with the cover determined by the exposed column and row spans.
-/

namespace Lax342547.NoCoverCertificate

open Lax342547.GreedySpans Lax342547.GreedyTails Lax342547.CoverProjection
open scoped BigOperators

axiom low_rank_cover_certificate {K V W ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : ι → V →ₗ[K] W) (r : ℝ) (k n : ℕ)
    (hM : ∀ i, (Module.finrank K (LinearMap.range (M i)) : ℝ) ≤ r)
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n)
    (hlow : (Module.finrank K (LinearMap.range (∑ i, M i)) : ℝ) < (2^(k-n) : ℝ)/4) :
    ∃ E J : Finset ι, Disjoint E J ∧ 2^(k-n) ≤ J.card ∧
      ∀ j ∈ J, projection (M j) (E.sup (fun i => LinearMap.range (M i)))
        (E.sup (fun i => LinearMap.range (M i).dualMap)) = 0

end Lax342547.NoCoverCertificate
