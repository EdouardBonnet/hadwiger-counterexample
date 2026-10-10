import Lax342547.ParameterCellAveraging
import Lax342547Proofs.CellAveraging

namespace Lax342547Proofs.ParameterCellAveraging
open Lax342547.ParameterCellAveraging

set_option backward.isDefEq.respectTransparency false
open Lax342547.CellAveraging Lax342547.RetainedImages

/--
---
conclusion: Lax342547.ParameterCellAveraging.average_mono
---
-/
theorem average_mono {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f g : A → B → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (h : ∀ x y, f x y ≤ g x y) :
    average p q f ≤ average p q g := by
  unfold average
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h x y) (mul_nonneg (hp x) (hq y))

/--
---
conclusion: Lax342547.ParameterCellAveraging.average_const
---
-/
theorem average_const {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) (c : ℝ) :
    average p q (fun _ _ => c) = c := by
  unfold average
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hp, hq, mul_one, one_mul]

/--
---
conclusion: Lax342547.ParameterCellAveraging.average_cell_pair_lower
---
-/
theorem average_cell_pair_lower {A B ΩA ΩB C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop)
    (valid : A → B → C → D → Prop) (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) (hτ : 0 < τ)
    (hloc : ∀ x y c d, valid x y c d → τ ≤ recordMass α (recordA x y) (acceptA x) c →
      τ ≤ recordMass β (recordB y x) (acceptB y) d → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA x a ∧ recordA x y a = c))
          (conditionalLaw β (fun b => acceptB y b ∧ recordB y x b = d)) H) :
    ε * average p q (fun x y => retainedPairs (recordMass α (recordA x y) (acceptA x))
      (recordMass β (recordB y x) (acceptB y)) (valid x y) τ) ≤ pairEventMass α β H := by
  have h := average_mono p q
    (fun x y => ε * retainedPairs (recordMass α (recordA x y) (acceptA x))
      (recordMass β (recordB y x) (acceptB y)) (valid x y) τ)
    (fun _ _ => pairEventMass α β H) hp hq
    (fun x y => Lax342547Proofs.CellAveraging.retained_cell_pair_lower α β (recordA x y) (recordB y x)
      (acceptA x) (acceptB y) (valid x y) H τ ε hα hβ hτ (hloc x y))
  rw [average_const p q hpsum hqsum] at h
  have he : average p q (fun x y => ε * retainedPairs (recordMass α (recordA x y) (acceptA x))
      (recordMass β (recordB y x) (acceptB y)) (valid x y) τ) =
      ε * average p q (fun x y => retainedPairs (recordMass α (recordA x y) (acceptA x))
        (recordMass β (recordB y x) (acceptB y)) (valid x y) τ) := by
    unfold average
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rwa [he] at h

end Lax342547Proofs.ParameterCellAveraging
