import Lax342547.KeyMeasures

namespace Lax342547Proofs.KeyMeasures
open Lax342547.KeyMeasures

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.KeyMeasures.key_mass_nonneg
---
-/
theorem key_mass_nonneg {Ω Q : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop) (hρ : ∀ ω, 0 ≤ ρ ω) (q : Q) :
    0 ≤ keyMass ρ key accepted q := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hρ ω
  · exact le_rfl

/--
---
conclusion: Lax342547.KeyMeasures.key_mass_total
---
-/
theorem key_mass_total {Ω Q : Type} [Fintype Ω] [Fintype Q]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop) : by
      classical
      exact (∑ q, keyMass ρ key accepted q) = ∑ ω, if accepted ω then ρ ω else 0 := by
  classical
  unfold keyMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : accepted ω
  · simp [h, eq_comm]
  · simp [h]

/--
---
conclusion: Lax342547.KeyMeasures.key_mass_subprobability
---
-/
theorem key_mass_subprobability {Ω Q : Type} [Fintype Ω] [Fintype Q]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hsum : ∑ ω, ρ ω ≤ 1) :
    (∑ q, keyMass ρ key accepted q) ≤ 1 := by
  classical
  rw [Lax342547.KeyMeasures.key_mass_total]
  apply le_trans _ hsum
  apply Finset.sum_le_sum
  intro ω _
  split_ifs
  · exact le_rfl
  · exact hρ ω

/--
---
conclusion: Lax342547.KeyMeasures.key_collision_identity
---
-/
theorem key_collision_identity {ΩA ΩB Q : Type} [Fintype ΩA] [Fintype ΩB] [Fintype Q]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (keyA : ΩA → Q) (keyB : ΩB → Q)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) : by
      classical
      exact (∑ q, keyMass α keyA acceptA q * keyMass β keyB acceptB q) =
        ∑ a, ∑ b, if acceptA a ∧ acceptB b ∧ keyA a = keyB b then α a * β b else 0 := by
  classical
  unfold keyMass
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : acceptA a <;> by_cases hb : acceptB b
  · simp [ha, hb, ite_mul, mul_ite, eq_comm]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]

/--
---
conclusion: Lax342547.KeyMeasures.uniform_overlap_collision
---
-/
theorem uniform_overlap_collision {Q : Type} [Fintype Q] [Nonempty Q] (a b : Q → ℝ) :
    uniformOverlap a b = Fintype.card Q * ∑ q, a q * b q := by
  have hcard : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformOverlap uniformDensity
  have hq (q : Q) : (Fintype.card Q : ℝ) * a q * (Fintype.card Q * b q) =
      (Fintype.card Q : ℝ)^2 * (a q * b q) := by ring
  simp only [hq, ← Finset.mul_sum]
  field_simp

end Lax342547Proofs.KeyMeasures
