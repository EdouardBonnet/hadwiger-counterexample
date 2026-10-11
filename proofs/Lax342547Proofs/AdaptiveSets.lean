import Lax342547.AdaptiveSets
import Lax342547.AdaptiveSampling
import Lax342547.CoordinateRestrictions

namespace Lax342547Proofs.AdaptiveSets
open Lax342547.AdaptiveSets

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.AdaptiveSets.embedding_adaptive_bound
---
-/
theorem embedding_adaptive_bound {E J ι Ω : Type} [Fintype E] [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq E] [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : E ⊕ J ↪ ι) (A : (E → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hA : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j, A (fun e => sample (a (.inl e))) (sample (a (.inr j)))) ≤ p^Fintype.card J := by
  classical
  have hh := Lax342547.CoordinateRestrictions.embedding_restriction μ a
    (fun t : E ⊕ J → Ω => ∀ j, A (fun e => t (.inl e)) (t (.inr j))) hμ
  rw [hh]
  exact Lax342547.AdaptiveSampling.adaptive_cylinder_bound μ A p hμ hA

/--
---
conclusion: Lax342547.AdaptiveSets.disjoint_adaptive_bound
---
-/
theorem disjoint_adaptive_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E J : Finset ι) (h : Disjoint E J)
    (A : (E → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hA : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j ∈ J, A (fun e => sample e.val) (sample j)) ≤ p^J.card := by
  classical
  have hh := Lax342547.AdaptiveSets.embedding_adaptive_bound μ (disjointEmbedding E J h) A p hμ hA
  have he : (fun sample : ι → Ω => ∀ j : J, A (fun e => sample e.val) (sample j.val)) =
      (fun sample : ι → Ω => ∀ j ∈ J, A (fun e => sample e.val) (sample j)) := by
    funext sample
    apply propext
    exact ⟨fun hh j hj => hh ⟨j,hj⟩,fun hh j => hh j.val j.property⟩
  change cellMass (productLaw (fun _ : ι => μ))
    (fun sample => ∀ j : J, A (fun e => sample e.val) (sample j.val)) ≤ p^Fintype.card J at hh
  rw [he,Fintype.card_coe] at hh
  exact hh

end Lax342547Proofs.AdaptiveSets
