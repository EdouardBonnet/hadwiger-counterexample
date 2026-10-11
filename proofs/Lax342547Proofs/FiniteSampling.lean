import Lax342547.FiniteSampling
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Lax342547Proofs.FiniteSampling
open Lax342547.FiniteSampling

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.FiniteSampling.product_probability
---
-/
theorem product_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : ι → Ω → ℝ) (hμ : ∀ i, Probability (μ i)) : Probability (productLaw μ) := by
  classical
  constructor
  · intro sample
    exact Finset.prod_nonneg (fun i _ => (hμ i).1 (sample i))
  · unfold productLaw
    rw [← Fintype.prod_sum]
    simp [fun i => (hμ i).2]

/--
---
conclusion: Lax342547.FiniteSampling.cylinder_probability
---
-/
theorem cylinder_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : ι → Ω → ℝ) (A : ι → Ω → Prop) :
    cellMass (productLaw μ) (fun sample => ∀ i, A i (sample i)) = ∏ i, cellMass (μ i) (A i) := by
  classical
  unfold cellMass productLaw
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases ha : ∀ i, A i (sample i)
  · simp [ha]
  · have hh : (∏ i, if A i (sample i) then μ i (sample i) else 0) = 0 := by
      push Not at ha
      obtain ⟨i,hi⟩ := ha
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    simp [ha,hh]

/--
---
conclusion: Lax342547.FiniteSampling.coordinate_set_probability
---
-/
theorem coordinate_set_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (T : Finset ι) (S : Ω → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun sample => ∀ i ∈ T, S (sample i)) =
      (cellMass μ S)^T.card := by
  classical
  have h := Lax342547.FiniteSampling.cylinder_probability (fun _ : ι => μ) (fun i x => i ∈ T → S x)
  have hc (i : ι) : cellMass μ (fun x => i ∈ T → S x) = if i ∈ T then cellMass μ S else 1 := by
    by_cases hi : i ∈ T
    · simp [hi]
    · simp [cellMass,hi,hμ.2]
  simp_rw [hc] at h
  simpa using h

/--
---
conclusion: Lax342547.FiniteSampling.cell_mass_mono
---
-/
theorem cell_mass_mono {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (S T : Ω → Prop) (hρ : ∀ x, 0 ≤ ρ x) (hST : ∀ x, S x → T x) :
    cellMass ρ S ≤ cellMass ρ T := by
  classical
  unfold cellMass
  apply Finset.sum_le_sum
  intro x _
  by_cases hs : S x
  · simp [hs,hST x hs]
  · simp [hs]
    split_ifs
    · exact hρ x
    · exact le_rfl

/--
---
conclusion: Lax342547.FiniteSampling.cell_mass_union_bound
---
-/
theorem cell_mass_union_bound {Ω J : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (A : J → Ω → Prop) (T : Finset J) (hρ : ∀ x, 0 ≤ ρ x) :
    cellMass ρ (fun x => ∃ j ∈ T, A j x) ≤ ∑ j ∈ T, cellMass ρ (A j) := by
  classical
  unfold cellMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : ∃ j ∈ T, A j x
  · rw [if_pos ha]
    obtain ⟨j,hj,hA⟩ := ha
    have hh := Finset.single_le_sum (s := T) (f := fun j => if A j x then ρ x else 0)
      (fun i _ => by split_ifs; exact hρ x; exact le_rfl) hj
    simpa [hA] using hh
  · rw [if_neg ha]
    exact Finset.sum_nonneg (fun j _ => by split_ifs; exact hρ x; exact le_rfl)

/--
---
conclusion: Lax342547.FiniteSampling.exceptional_positions_bound
---
-/
theorem exceptional_positions_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (S : Ω → Prop) (k : ℕ) (hμ : Probability μ) : by
      classical
      exact cellMass (productLaw (fun _ : ι => μ))
          (fun sample => k ≤ (Finset.univ.filter (fun i => S (sample i))).card) ≤
        (Fintype.card ι).choose k*(cellMass μ S)^k := by
  classical
  let candidates := (Finset.univ : Finset ι).powersetCard k
  have hcover : ∀ sample : ι → Ω,
      k ≤ (Finset.univ.filter (fun i => S (sample i))).card →
        ∃ T ∈ candidates, ∀ i ∈ T, S (sample i) := by
    intro sample hs
    obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hs
    refine ⟨T,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩,?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hT hi)).2
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : ι => μ) (fun _ => hμ)
  calc
    _ ≤ cellMass (productLaw (fun _ : ι => μ))
        (fun sample => ∃ T ∈ candidates, ∀ i ∈ T, S (sample i)) :=
      Lax342547.FiniteSampling.cell_mass_mono _ _ _ hprob.1 hcover
    _ ≤ ∑ T ∈ candidates, cellMass (productLaw (fun _ : ι => μ)) (fun sample => ∀ i ∈ T, S (sample i)) :=
      Lax342547.FiniteSampling.cell_mass_union_bound _ _ candidates hprob.1
    _ = (Fintype.card ι).choose k*(cellMass μ S)^k := by
      have ht : ∀ T ∈ candidates, cellMass (productLaw (fun _ : ι => μ))
          (fun sample => ∀ i ∈ T, S (sample i)) = (cellMass μ S)^k := by
        intro T hT
        rw [Lax342547.FiniteSampling.coordinate_set_probability μ T S hμ,(Finset.mem_powersetCard.mp hT).2]
      rw [Finset.sum_congr rfl ht,Finset.sum_const,Finset.card_powersetCard,Finset.card_univ]
      simp [nsmul_eq_mul]

end Lax342547Proofs.FiniteSampling
