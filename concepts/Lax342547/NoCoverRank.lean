import Lax342547.NoCoverCertificate
import Lax342547.CoverClasses
import Lax342547.AdaptiveUnion

/-!
---
title: Rank growth without an adaptive mode cover
type: lemma
---
Actual low rank sums force a cover based on exposed indices; conditioning on those indices and taking the finite union yields a checked no-cover probability bound for any join-stable cover classes.
-/

namespace Lax342547.NoCoverRank

open Lax342547.CoverProjection Lax342547.CoverClasses
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom no_cover_rank_probability {K V W ι Ω : Type} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (μ : Ω → ℝ) (M : Ω → V →ₗ[K] W) (P : Submodule K W → Prop)
    (Q : Submodule K (Module.Dual K V) → Prop) (r p : ℝ) (k n : ℕ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r)
    (hM : ∀ x, (Module.finrank K (LinearMap.range (M x)) : ℝ) ≤ r)
    (hP : JoinClosed P) (hQ : JoinClosed Q)
    (hPC : ∀ x, P (LinearMap.range (M x))) (hQR : ∀ x, Q (LinearMap.range (M x).dualMap))
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n)
    (hcover : ∀ S T, P S → Q T →
      (Module.finrank K S : ℝ) ≤ r*Fintype.card ι →
      (Module.finrank K T : ℝ) ≤ r*Fintype.card ι →
      cellMass μ (fun x => projection (M x) S T = 0) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => (Module.finrank K (LinearMap.range (∑ i, M (sample i))) : ℝ) < (2^(k-n) : ℝ)/4) ≤
      (4 : ℝ)^Fintype.card ι*p^(2^(k-n))

end Lax342547.NoCoverRank
