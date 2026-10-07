import Lax342547.FractionalColoring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Lax342547Proofs.FractionalColoring

open Lax342547.FractionalColoring
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def ofColoring {k : ℕ} (C : G.Coloring (Fin k)) : Coloring G := by
  classical
  let fiber (c : Fin k) : Finset V := Finset.univ.filter (fun v ↦ C v = c)
  refine {
    weight := fun S ↦ ∑ c : Fin k, if S = fiber c then 1 else 0
    nonneg := fun S ↦ Finset.sum_nonneg (fun c _ ↦ by positivity)
    supported := ?_
    covers := ?_ }
  · intro S hS
    apply Finset.sum_eq_zero
    intro c _
    have hne : S ≠ fiber c := by
      intro heq
      apply hS
      subst S
      intro v hv w hw _ hadj
      exact C.valid hadj ((Finset.mem_filter.mp hv).2.trans
        (Finset.mem_filter.mp hw).2.symm)
    simp [hne]
  · intro v
    have hw : (1 : ℝ) ≤ ∑ c : Fin k, if fiber (C v) = fiber c then 1 else 0 := by
      have h := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun c : Fin k ↦ if fiber (C v) = fiber c then (1 : ℝ) else 0)
        (fun c _ ↦ by positivity) (Finset.mem_univ (C v))
      simpa using h
    have hv : v ∈ fiber (C v) := by simp [fiber]
    have h := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun S : Finset V ↦ if v ∈ S then
        (∑ c : Fin k, if S = fiber c then (1 : ℝ) else 0) else 0)
      (fun S _ ↦ by positivity) (Finset.mem_univ (fiber (C v)))
    exact hw.trans (by simpa only [if_pos hv] using h)

theorem totalWeight_ofColoring {k : ℕ} (C : G.Coloring (Fin k)) :
    totalWeight (ofColoring C) = k := by
  classical
  unfold totalWeight ofColoring
  dsimp only
  rw [Finset.sum_comm]
  simp

theorem costs_nonempty (G : SimpleGraph V) :
    Set.Nonempty {w : ℝ | ∃ C : Coloring G, totalWeight C = w} := by
  have hfinite : G.chromaticNumber ≠ ⊤ := by
    intro h
    have hle := G.chromaticNumber_le_card
    rw [h] at hle
    simp at hle
  obtain ⟨C⟩ := G.colorable_of_chromaticNumber_ne_top hfinite
  exact ⟨_, ofColoring C, rfl⟩

theorem costs_bddBelow (G : SimpleGraph V) :
    BddBelow {w : ℝ | ∃ C : Coloring G, totalWeight C = w} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨C, rfl⟩
  exact Finset.sum_nonneg (fun S _ ↦ C.nonneg S)

theorem card_le_twice_totalWeight (C : Coloring G) (hα : G.indepNum ≤ 2) :
    (Fintype.card V : ℝ) ≤ 2 * totalWeight C := by
  classical
  calc
    (Fintype.card V : ℝ) = ∑ _v : V, (1 : ℝ) := by simp
    _ ≤ ∑ v : V, ∑ S : Finset V, if v ∈ S then C.weight S else 0 :=
      Finset.sum_le_sum (fun v _ ↦ C.covers v)
    _ = ∑ S : Finset V, (S.card : ℝ) * C.weight S := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      simp
    _ ≤ ∑ S : Finset V, 2 * C.weight S := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : G.IsIndepSet (S : Set V)
      · have hcard : (S.card : ℝ) ≤ 2 := by exact_mod_cast hS.card_le_indepNum.trans hα
        exact mul_le_mul_of_nonneg_right hcard (C.nonneg S)
      · simp [C.supported S hS]
    _ = 2 * totalWeight C := by simp only [totalWeight, Finset.mul_sum]

/--
---
conclusion: Lax342547.FractionalColoring.fractional_chromatic_lower_bound
---
Sum the coverage inequalities over vertices, interchange the two finite
sums, and use the bound of two on every independent set.
-/
theorem fractional_chromatic_lower_bound (G : SimpleGraph V) (hα : G.indepNum ≤ 2) :
    (Fintype.card V : ℝ) / 2 ≤ fractionalChromaticNumber G := by
  apply le_csInf (costs_nonempty G)
  rintro _ ⟨C, rfl⟩
  have h := card_le_twice_totalWeight C hα
  linarith

/--
---
conclusion: Lax342547.FractionalColoring.fractional_chromatic_le_chromatic
---
Give each color class of an optimal ordinary coloring unit weight.
-/
theorem fractional_chromatic_le_chromatic (G : SimpleGraph V) :
    fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ) := by
  have hfinite : G.chromaticNumber ≠ ⊤ := by
    intro h
    have hle := G.chromaticNumber_le_card
    rw [h] at hle
    simp at hle
  obtain ⟨C⟩ := G.colorable_of_chromaticNumber_ne_top hfinite
  apply csInf_le (costs_bddBelow G)
  exact ⟨ofColoring C, totalWeight_ofColoring C⟩

end Lax342547Proofs.FractionalColoring
