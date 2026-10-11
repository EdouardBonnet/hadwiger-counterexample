import Lax342547.AdaptiveSampling
import Lax342547.FiniteSampling

namespace Lax342547Proofs.AdaptiveSampling
open Lax342547.AdaptiveSampling

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.AdaptiveSampling.adaptive_cylinder_probability
---
-/
theorem adaptive_cylinder_probability {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K] (μ : Ω → ℝ) (A : (J → Ω) → Ω → Prop) :
    cellMass (productLaw (fun _ : J ⊕ K => μ))
      (fun sample => ∀ k, A (fun j => sample (.inl j)) (sample (.inr k))) =
      ∑ exposed : J → Ω, productLaw (fun _ : J => μ) exposed*(cellMass μ (A exposed))^Fintype.card K := by
  classical
  let e := (Equiv.sumPiEquivProdPi (fun _ : J ⊕ K => Ω)).symm
  have he (exposed : J → Ω) (free : K → Ω) : e (exposed,free) = Sum.elim exposed free := by rfl
  unfold cellMass
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro exposed _
  simp_rw [he]
  simp only [Sum.elim_inl,Sum.elim_inr]
  have hh := Lax342547.FiniteSampling.cylinder_probability
    (fun _ : K => μ) (fun _ => A exposed)
  simp only [Finset.prod_const,Finset.card_univ] at hh
  calc
    _ = productLaw (fun _ : J => μ) exposed*
        cellMass (productLaw (fun _ : K => μ)) (fun free => ∀ k, A exposed (free k)) := by
      unfold cellMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro free _
      by_cases ha : ∀ k, A exposed (free k)
      · simp [ha,productLaw,Fintype.prod_sum_type]
      · simp [ha]
    _ = _ := by rw [hh]; rfl

/--
---
conclusion: Lax342547.AdaptiveSampling.adaptive_cylinder_bound
---
-/
theorem adaptive_cylinder_bound {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K] (μ : Ω → ℝ) (A : (J → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hp : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : J ⊕ K => μ))
      (fun sample => ∀ k, A (fun j => sample (.inl j)) (sample (.inr k))) ≤ p^Fintype.card K := by
  classical
  rw [Lax342547.AdaptiveSampling.adaptive_cylinder_probability]
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : J => μ) (fun _ => hμ)
  calc
    _ ≤ ∑ exposed : J → Ω, productLaw (fun _ : J => μ) exposed*p^Fintype.card K := by
      apply Finset.sum_le_sum
      intro exposed _
      have hn : 0 ≤ cellMass μ (A exposed) := by
        unfold cellMass
        exact Finset.sum_nonneg (fun x _ => by split_ifs; exact hμ.1 x; exact le_rfl)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn (hp exposed) _) (hprob.1 exposed)
    _ = _ := by rw [← Finset.sum_mul,hprob.2,one_mul]

end Lax342547Proofs.AdaptiveSampling
