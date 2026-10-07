import Lax342547.GradientForm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Lax342547Proofs.GradientForm

open Lax342547.MomentSpace Lax342547.GradientForm

variable {X Tag : Type} [AddCommGroup X] [Module Binary X] [Fintype Tag]

theorem rankOne_apply (a b : X →ₗ[Binary] Binary) (x y : X) :
    rankOne a b x y = a x * b y := rfl

/--
---
conclusion: Lax342547.GradientForm.form_properties
---
Interchanging arguments permutes the symmetrized terms. On the diagonal
each such pair cancels in characteristic two, and each binary scalar
squares to itself.
-/
theorem form_properties (a : X →ₗ[Binary] Binary) (aTag bTag : Tag → X →ₗ[Binary] Binary)
    (B : LinearMap.BilinForm Binary X) :
    (∀ x y, form a aTag bTag B x y = form a aTag bTag B y x) ∧
      ∀ x, form a aTag bTag B x x = a x := by
  have hf (x y : X) : form a aTag bTag B x y =
      a x * a y + (∑ t, (aTag t x * bTag t y + bTag t x * aTag t y)) + B x y + B y x := by
    simp [form, rankOne_apply, LinearMap.sum_apply]
  constructor
  · intro x y
    rw [hf, hf]
    have hs : (∑ t, (aTag t x * bTag t y + bTag t x * aTag t y)) =
        ∑ t, (aTag t y * bTag t x + bTag t y * aTag t x) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hs]
    ring
  · intro x
    rw [hf]
    have hs : (∑ t, (aTag t x * bTag t x + bTag t x * aTag t x)) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [mul_comm (bTag t x), ZModModule.add_self]
    rw [hs, add_zero, add_assoc, ZModModule.add_self, add_zero]
    have hb (z : Binary) : z * z = z := by fin_cases z <;> rfl
    exact hb (a x)

end Lax342547Proofs.GradientForm
