import Lax342547.Walsh
import Lax342547Proofs.FiniteLinearLaw
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Lax342547Proofs.Walsh

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.Walsh

theorem binary_cases (z : Binary) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

theorem sign_add (a b : Binary) : sign (a + b) = sign a * sign b := by
  rcases binary_cases a with rfl | rfl <;> rcases binary_cases b with rfl | rfl <;>
    simp [show (1 + 1 : Binary) = 0 from rfl]

theorem sign_eq_one_iff (z : Binary) : sign z = 1 ↔ z = 0 := by
  rcases binary_cases z with rfl | rfl <;> norm_num

theorem phase_comm {I : Type} [Fintype I] (x y : I → Binary) : phase x y = phase y x := by
  rw [phase, phase, dotProduct_comm]

/--
---
conclusion: Lax342547.Walsh.linear_orthogonality
---
Compose the nontrivial real binary character with the linear functional.
Its being the trivial character would force the functional to vanish,
so the finite additive-character orthogonality theorem gives zero sum.
-/
theorem linear_orthogonality {V : Type} [AddCommGroup V] [Module Binary V] [Fintype V]
    (f : V →ₗ[Binary] Binary) (hf : f ≠ 0) : ∑ x, sign (f x) = 0 := by
  classical
  let ψ : AddChar V ℝ :=
    { toFun := fun x => sign (f x)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun x y => by rw [map_add, sign_add] }
  change ∑ x, ψ x = 0
  apply (AddChar.sum_eq_zero_iff_ne_zero (ψ := ψ)).mpr
  intro h
  apply hf
  ext x
  have hx := AddChar.eq_zero_iff.mp h x
  exact (sign_eq_one_iff (f x)).mp hx

theorem sum_phase {I : Type} [Fintype I] [DecidableEq I] (x : I → Binary) :
    ∑ y, phase x y = if x = 0 then (2 : ℝ) ^ Fintype.card I else 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [phase]
  · rw [if_neg hx]
    let f : (I → Binary) →ₗ[Binary] Binary :=
      { toFun := fun y => dotProduct x y
        map_add' := fun _ _ => dotProduct_add _ _ _
        map_smul' := fun _ _ => dotProduct_smul _ _ _ }
    apply linear_orthogonality f
    intro hf
    apply hx
    exact dotProduct_eq_zero x (fun y => congrArg (fun g : (I → Binary) →ₗ[Binary] Binary => g y) hf)

/--
---
conclusion: Lax342547.Walsh.orthogonality
---
The product of the two signs is the character indexed by x+z.
It is trivial exactly when x=z in the binary vector space.
-/
theorem orthogonality {I : Type} [Fintype I] [DecidableEq I] (x z : I → Binary) :
    ∑ y, phase x y * phase z y = if x = z then (2 : ℝ) ^ Fintype.card I else 0 := by
  have h (y : I → Binary) : phase x y * phase z y = phase (x + z) y := by
    rw [phase, phase, phase, add_dotProduct, sign_add]
  simp_rw [h]
  rw [sum_phase]
  have he : x + z = 0 ↔ x = z := by
    constructor
    · intro h
      calc
        x = x + (z + z) := by rw [ZModModule.add_self, add_zero]
        _ = (x + z) + z := (add_assoc _ _ _).symm
        _ = z := by rw [h, zero_add]
    · rintro rfl
      exact ZModModule.add_self _
  simp only [he]

theorem sum_square_expand {X Y : Type} [Fintype X] [Fintype Y]
    (H : X → Y → ℝ) (f : Y → ℝ) :
    ∑ x, (∑ y, H x y * f y) ^ 2 =
      ∑ y, ∑ z, f y * f z * ∑ x, H x y * H x z := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  ring

/--
---
conclusion: Lax342547.Walsh.transform_energy
---
Expand the square and interchange the three finite sums. Orthogonality
kills every off-diagonal pair and contributes exactly 2^d on the diagonal.
-/
theorem transform_energy {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Binary) → ℝ) :
    ∑ x, (transform f x) ^ 2 = (2 : ℝ) ^ Fintype.card I * ∑ y, (f y) ^ 2 := by
  classical
  unfold transform
  rw [sum_square_expand]
  simp_rw [phase_comm, orthogonality]
  simp [mul_ite, Finset.mul_sum, pow_two, mul_comm]

/--
---
conclusion: Lax342547.Walsh.dot_correlation_sq
---
Apply finite Cauchy-Schwarz to one weight and the Walsh transform of the
other, then substitute the exact transform energy identity.
-/
theorem dot_correlation_sq {I : Type} [Fintype I] [DecidableEq I]
    (f g : (I → Binary) → ℝ) :
    (∑ x, ∑ y, f x * g y * phase x y) ^ 2 ≤
      (2 : ℝ) ^ Fintype.card I * (∑ x, (f x) ^ 2) * ∑ y, (g y) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (transform g)
  rw [transform_energy] at h
  calc
    _ = (∑ x, f x * transform g x) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp only [transform, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ _ := h
    _ = _ := by ring

theorem weight_energy_bound {X : Type} [Fintype X] [Nonempty X]
    (α f : X → ℝ) (p : ℝ) (hα : ∀ x, 0 ≤ α x ∧ α x ≤ p)
    (hαsum : ∑ x, α x ≤ 1) (hf : ∀ x, |f x| ≤ 1) :
    ∑ x, (α x * f x) ^ 2 ≤ p := by
  have hp : 0 ≤ p := (hα (Classical.arbitrary X)).1.trans (hα (Classical.arbitrary X)).2
  calc
    _ ≤ ∑ x, p * α x := by
      apply Finset.sum_le_sum
      intro x _
      have hfx : (f x) ^ 2 ≤ 1 := by
        have h := abs_le.mp (hf x)
        nlinarith
      have hax := hα x
      calc
        _ = (α x) ^ 2 * (f x) ^ 2 := mul_pow _ _ _
        _ ≤ (α x) ^ 2 * 1 := mul_le_mul_of_nonneg_left hfx (sq_nonneg _)
        _ ≤ p * α x := by nlinarith
    _ = p * ∑ x, α x := (Finset.mul_sum _ _ _).symm
    _ ≤ p * 1 := mul_le_mul_of_nonneg_left hαsum hp
    _ = p := mul_one _

/--
---
conclusion: Lax342547.Walsh.subprobability_dot_bound
---
Absorb each subprobability mass into its bounded weight. Its squared
energy is at most its point-mass cap times its total mass, hence at most
the cap. The squared Walsh bound and a square root give Lemma 4.6(b).
-/
theorem subprobability_dot_bound {I : Type} [Fintype I] [DecidableEq I]
    (α β f g : (I → Binary) → ℝ) (p₁ p₂ : ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ p₁) (hβ : ∀ y, 0 ≤ β y ∧ β y ≤ p₂)
    (hαsum : ∑ x, α x ≤ 1) (hβsum : ∑ y, β y ≤ 1)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |∑ x, ∑ y, α x * β y * f x * g y * phase x y| ≤
      Real.sqrt ((2 : ℝ) ^ Fintype.card I * p₁ * p₂) := by
  have h := dot_correlation_sq (fun x => α x * f x) (fun y => β y * g y)
  have hαE := weight_energy_bound α f p₁ hα hαsum hf
  have hβE := weight_energy_bound β g p₂ hβ hβsum hg
  have hp₁ : 0 ≤ p₁ := (hα 0).1.trans (hα 0).2
  have hp₂ : 0 ≤ p₂ := (hβ 0).1.trans (hβ 0).2
  have hs : (∑ x, ∑ y, α x * β y * f x * g y * phase x y) ^ 2 ≤
      (2 : ℝ) ^ Fintype.card I * p₁ * p₂ := by
    calc
      _ = (∑ x, ∑ y, (α x * f x) * (β y * g y) * phase x y) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  exact Real.abs_le_sqrt hs

end Lax342547Proofs.Walsh
