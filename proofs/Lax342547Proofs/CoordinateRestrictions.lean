import Lax342547.CoordinateRestrictions
import Lax342547Proofs.FiniteSampling
import Mathlib.Logic.Equiv.Set

namespace Lax342547Proofs.CoordinateRestrictions
open Lax342547.CoordinateRestrictions

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.CoordinateRestrictions.complete_left
---
-/
theorem complete_left {J ι : Type} (a : J ↪ ι) (j : J) : complete a (.inl j) = a j := by
  rfl

/--
---
conclusion: Lax342547.CoordinateRestrictions.sum_restriction
---
-/
theorem sum_restriction {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K]
    (μ : Ω → ℝ) (A : (J → Ω) → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : J ⊕ K => μ)) (fun sample => A (fun j => sample (.inl j))) =
      cellMass (productLaw (fun _ : J => μ)) A := by
  classical
  let e := (Equiv.sumPiEquivProdPi (fun _ : J ⊕ K => Ω)).symm
  unfold cellMass
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  have ht := (Lax342547Proofs.FiniteSampling.product_probability (fun _ : K => μ) (fun _ => hμ)).2
  apply Finset.sum_congr rfl
  intro sample _
  change (∑ free : K → Ω, if A sample then
    productLaw (fun _ : J ⊕ K => μ) (Sum.elim sample free) else 0) =
      if A sample then productLaw (fun _ : J => μ) sample else 0
  by_cases ha : A sample
  · simp only [ha,ite_true,productLaw,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
    rw [← Finset.mul_sum]
    change (∏ i, μ (sample i))*(∑ free : K → Ω, productLaw (fun _ : K => μ) free) = _
    rw [ht,mul_one]
  · simp [ha]

/--
---
conclusion: Lax342547.CoordinateRestrictions.embedding_restriction
---
-/
theorem embedding_restriction {J ι Ω : Type} [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : J ↪ ι) (A : (J → Ω) → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun sample => A (fun j => sample (a j))) =
      cellMass (productLaw (fun _ : J => μ)) A := by
  classical
  let K := {i : ι // i ∉ Set.range a}
  let e := complete a
  let fe := Equiv.piCongrLeft (fun _ : ι => Ω) e
  unfold cellMass
  rw [← fe.sum_comp]
  have hval (sample : J ⊕ K → Ω) : productLaw (fun _ : ι => μ) (fe sample) =
      productLaw (fun _ : J ⊕ K => μ) sample := by
    unfold productLaw
    rw [← e.prod_comp]
    dsimp [fe]
    simp only [Equiv.piCongrLeft_apply_apply]
    rfl
  have harg (sample : J ⊕ K → Ω) : (fun j => fe sample (a j)) = fun j => sample (.inl j) := by
    funext j
    rw [← complete_left a j]
    exact Equiv.piCongrLeft_apply_apply (fun _ : ι => Ω) e sample (.inl j)
  simp_rw [harg,hval]
  exact sum_restriction μ A hμ

end Lax342547Proofs.CoordinateRestrictions
