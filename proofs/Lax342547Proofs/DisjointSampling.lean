import Lax342547.DisjointSampling
import Mathlib.Logic.Equiv.Prod
import Lax342547.CellAveraging
import Lax342547.CoordinateRestrictions
import Lax342547.FiniteSampling

namespace Lax342547Proofs.DisjointSampling
open Lax342547.DisjointSampling

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.CellAveraging
open scoped BigOperators

/--
---
conclusion: Lax342547.DisjointSampling.pair_samples_left
---
-/
theorem pair_samples_left {J Ω : Type} (sample : J → Ω × Ω) (j : J) :
    pairSamples sample (j,false) = (sample j).1 := by
  rfl

/--
---
conclusion: Lax342547.DisjointSampling.pair_samples_right
---
-/
theorem pair_samples_right {J Ω : Type} (sample : J → Ω × Ω) (j : J) :
    pairSamples sample (j,true) = (sample j).2 := by
  rfl

/--
---
conclusion: Lax342547.DisjointSampling.paired_product_probability
---
-/
theorem paired_product_probability {J Ω : Type} [Fintype J] [Fintype Ω] [DecidableEq J]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) :
    cellMass (productLaw (fun _ : J × Bool => μ))
      (fun sample => ∀ j, E (sample (j,false)) (sample (j,true))) =
        (pairEventMass μ μ E)^Fintype.card J := by
  classical
  have h := Lax342547.FiniteSampling.cylinder_probability
    (fun _ : J => fun xy : Ω × Ω => μ xy.1*μ xy.2) (fun _ xy => E xy.1 xy.2)
  have hmass : cellMass (fun xy : Ω × Ω => μ xy.1*μ xy.2) (fun xy => E xy.1 xy.2) = pairEventMass μ μ E := by
    simp only [cellMass,pairEventMass,Fintype.sum_prod_type]
  simp only [hmass,Finset.prod_const,Finset.card_univ] at h
  rw [← h]
  unfold cellMass
  rw [← (pairSamples (J := J) (Ω := Ω)).sum_comp]
  apply Finset.sum_congr rfl
  intro sample _
  simp only [Lax342547.DisjointSampling.pair_samples_left,Lax342547.DisjointSampling.pair_samples_right]
  split_ifs
  · unfold productLaw
    simp only [Fintype.prod_prod_type,Fintype.prod_bool,Lax342547.DisjointSampling.pair_samples_left,Lax342547.DisjointSampling.pair_samples_right]
    apply Finset.prod_congr rfl
    intro j _
    ring
  · rfl

/--
---
conclusion: Lax342547.DisjointSampling.disjoint_pair_probability
---
-/
theorem disjoint_pair_probability {J ι Ω : Type} [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : J × Bool ↪ ι) (E : Ω → Ω → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) =
        (pairEventMass μ μ E)^Fintype.card J := by
  rw [Lax342547.CoordinateRestrictions.embedding_restriction μ a
    (fun sample => ∀ j, E (sample (j,false)) (sample (j,true))) hμ]
  exact Lax342547.DisjointSampling.paired_product_probability μ E

/--
---
conclusion: Lax342547.DisjointSampling.disjoint_pair_exception_bound
---
-/
theorem disjoint_pair_exception_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (k : ℕ) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∃ a : Fin k × Bool ↪ ι,
        ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) ≤
      (Fintype.card ι)^(2*k)*(pairEventMass μ μ E)^k := by
  classical
  let choices := (Finset.univ : Finset (Fin k × Bool ↪ ι))
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : ι => μ) (fun _ => hμ)
  have hbound := Lax342547.FiniteSampling.cell_mass_union_bound
    (productLaw (fun _ : ι => μ))
    (fun a : Fin k × Bool ↪ ι => fun sample => ∀ j, E (sample (a (j,false))) (sample (a (j,true))))
    choices hprob.1
  simp only [choices,Finset.mem_univ,true_and] at hbound
  have hlocal : ∀ a : Fin k × Bool ↪ ι,
      cellMass (productLaw (fun _ : ι => μ))
        (fun sample => ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) = (pairEventMass μ μ E)^k := by
    intro a
    simpa using Lax342547.DisjointSampling.disjoint_pair_probability μ a E hμ
  simp_rw [hlocal] at hbound
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hbound
  have hcard : Fintype.card (Fin k × Bool ↪ ι) ≤ (Fintype.card ι)^(2*k) := by
    have hh := Fintype.card_le_of_injective (fun a : Fin k × Bool ↪ ι => (a : Fin k × Bool → ι))
      (fun _ _ h => Function.Embedding.coe_injective h)
    simpa [Fintype.card_fun,Fintype.card_prod,Nat.mul_comm] using hh
  have hmass := Lax342547.CellAveraging.pair_event_mass_nonneg μ μ E hμ.1 hμ.1
  exact hbound.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hmass k))

end Lax342547Proofs.DisjointSampling
