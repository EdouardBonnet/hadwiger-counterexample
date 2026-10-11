import Lax342547.CellAveraging

namespace Lax342547Proofs.CellAveraging
open Lax342547.CellAveraging

set_option backward.isDefEq.respectTransparency true
open Lax342547.RetainedImages Lax342547.CollisionPruning

/--
---
conclusion: Lax342547.CellAveraging.conditional_rectangle_mass
---
-/
theorem conditional_rectangle_mass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (H : ΩA → ΩB → Prop) :
    pairEventMass (conditionalLaw α C) (conditionalLaw β D) H =
      rectangleMass α β C D H / (cellMass α C * cellMass β D) := by
  classical
  unfold rectangleMass pairEventMass
  have ht (a : ΩA) (b : ΩB) : (if H a b then conditionalLaw α C a * conditionalLaw β D b else 0) =
      (if C a ∧ D b ∧ H a b then α a * β b else 0) / (cellMass α C * cellMass β D) := by
    by_cases hc : C a <;> by_cases hd : D b <;> by_cases hh : H a b <;>
      simp [conditionalLaw, hc, hd, hh, div_mul_div_comm]
  simp only [ht, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

/--
---
conclusion: Lax342547.CellAveraging.conditional_rectangle_lower
---
-/
theorem conditional_rectangle_lower {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (C : ΩA → Prop) (D : ΩB → Prop)
    (H : ΩA → ΩB → Prop) (ε : ℝ)
    (hC : 0 < cellMass α C) (hD : 0 < cellMass β D)
    (h : ε ≤ pairEventMass (conditionalLaw α C) (conditionalLaw β D) H) :
    ε * (cellMass α C * cellMass β D) ≤ rectangleMass α β C D H := by
  rw [Lax342547.CellAveraging.conditional_rectangle_mass] at h
  exact (le_div_iff₀ (mul_pos hC hD)).mp h

/--
---
conclusion: Lax342547.CellAveraging.partition_rectangle_mass
---
-/
theorem partition_rectangle_mass {ΩA ΩB C D : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (recordA : ΩA → C) (recordB : ΩB → D)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) (valid : C → D → Prop)
    (H : ΩA → ΩB → Prop) : by
      classical
      exact (∑ c, ∑ d, if valid c d then
        rectangleMass α β (fun a => acceptA a ∧ recordA a = c)
          (fun b => acceptB b ∧ recordB b = d) H else 0) =
        pairEventMass α β (fun a b => acceptA a ∧ acceptB b ∧ valid (recordA a) (recordB b) ∧ H a b) := by
  classical
  unfold rectangleMass pairEventMass
  have hs (c : C) (d : D) : (if valid c d then
      ∑ a, ∑ b, if (acceptA a ∧ recordA a = c) ∧ (acceptB b ∧ recordB b = d) ∧ H a b
        then α a * β b else 0 else 0) =
      ∑ a, ∑ b, if valid c d ∧ (acceptA a ∧ recordA a = c) ∧ (acceptB b ∧ recordB b = d) ∧ H a b
        then α a * β b else 0 := by
    by_cases hv : valid c d <;> simp [hv]
  have hchange : (∑ c, ∑ d, if valid c d then
      ∑ a, ∑ b, if (acceptA a ∧ recordA a = c) ∧ (acceptB b ∧ recordB b = d) ∧ H a b
        then α a * β b else 0 else 0) =
      ∑ c, ∑ d, ∑ a, ∑ b,
        if valid c d ∧ (acceptA a ∧ recordA a = c) ∧ (acceptB b ∧ recordB b = d) ∧ H a b
          then α a * β b else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    exact hs c d
  convert hchange.trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> rfl
    · rfl
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : acceptA a <;> by_cases hb : acceptB b <;> by_cases hh : H a b <;>
    simp [ha, hb, hh, eq_comm, ite_and]

  symm
  rw [Finset.sum_eq_single (recordA a)]
  · rw [Finset.sum_eq_single (recordB b)]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  · intro c _ hc
    simp [hc]
  · simp

/--
---
conclusion: Lax342547.CellAveraging.pair_event_mass_nonneg
---
-/
theorem pair_event_mass_nonneg {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (H : ΩA → ΩB → Prop)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) : 0 ≤ pairEventMass α β H := by
  classical
  unfold pairEventMass
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact mul_nonneg (hα a) (hβ b)
  · exact le_rfl

/--
---
conclusion: Lax342547.CellAveraging.retained_cell_pair_lower
---
-/
theorem retained_cell_pair_lower {ΩA ΩB C D : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (recordA : ΩA → C) (recordB : ΩB → D)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) (valid : C → D → Prop)
    (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) (hτ : 0 < τ)
    (hloc : ∀ c d, valid c d → τ ≤ recordMass α recordA acceptA c →
      τ ≤ recordMass β recordB acceptB d → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA a ∧ recordA a = c))
          (conditionalLaw β (fun b => acceptB b ∧ recordB b = d)) H) :
    ε * retainedPairs (recordMass α recordA acceptA) (recordMass β recordB acceptB) valid τ ≤
      pairEventMass α β H := by
  classical
  have hrect : ε * retainedPairs (recordMass α recordA acceptA) (recordMass β recordB acceptB) valid τ ≤
      ∑ c, ∑ d, if valid c d then
        rectangleMass α β (fun a => acceptA a ∧ recordA a = c)
          (fun b => acceptB b ∧ recordB b = d) H else 0 := by
    unfold retainedPairs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    by_cases hc : valid c d ∧ τ ≤ recordMass α recordA acceptA c ∧ τ ≤ recordMass β recordB acceptB d
    · rw [if_pos hc, if_pos hc.1]
      exact Lax342547.CellAveraging.conditional_rectangle_lower α β _ _ H ε
        (lt_of_lt_of_le hτ hc.2.1) (lt_of_lt_of_le hτ hc.2.2) (hloc c d hc.1 hc.2.1 hc.2.2)
    · rw [if_neg hc, mul_zero]
      split_ifs
      · exact Lax342547.CellAveraging.pair_event_mass_nonneg α β _ hα hβ
      · exact le_rfl
  rw [Lax342547.CellAveraging.partition_rectangle_mass] at hrect
  apply hrect.trans
  unfold pairEventMass
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases hh : acceptA a ∧ acceptB b ∧ valid (recordA a) (recordB b) ∧ H a b
  · rw [if_pos hh, if_pos hh.2.2.2]
  · rw [if_neg hh]
    split_ifs
    · exact mul_nonneg (hα a) (hβ b)
    · exact le_rfl

end Lax342547Proofs.CellAveraging
