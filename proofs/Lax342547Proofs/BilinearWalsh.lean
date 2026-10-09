import Lax342547.BilinearWalsh
import Lax342547Proofs.Walsh

namespace Lax342547Proofs.BilinearWalsh

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.BilinearWalsh

noncomputable def pushWeight {X Y : Type} [Fintype Y] [DecidableEq X]
    (T : Y → X) (g : Y → ℝ) (x : X) : ℝ :=
  ∑ y ∈ Finset.univ.filter (fun y => T y = x), g y

theorem pushWeight_sum {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (T : Y → X) (g : Y → ℝ) (f : X → ℝ) :
    ∑ x, f x * pushWeight T g x = ∑ y, f (T y) * g y := by
  classical
  simp only [pushWeight, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem pushWeight_energy {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (T : Y → X) (g : Y → ℝ) (K : ℕ)
    (hK : ∀ x, (Finset.univ.filter (fun y => T y = x)).card ≤ K) :
    ∑ x, (pushWeight T g x) ^ 2 ≤ (K : ℝ) * ∑ y, (g y) ^ 2 := by
  classical
  calc
    _ ≤ ∑ x, (K : ℝ) * pushWeight T (fun y => (g y) ^ 2) x := by
      apply Finset.sum_le_sum
      intro x _
      have h := Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ.filter (fun y => T y = x)) (fun _ => (1 : ℝ)) g
      have h' : (pushWeight T g x) ^ 2 ≤
          ((Finset.univ.filter (fun y => T y = x)).card : ℝ) *
            pushWeight T (fun y => (g y) ^ 2) x := by
        simpa only [pushWeight, one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h
      refine h'.trans ?_
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hK x)
      dsimp only [pushWeight]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    _ = _ := pushWeight_sum T (fun y => (g y) ^ 2) (fun _ => (K : ℝ)) |>.trans
      (Finset.mul_sum _ _ _).symm

theorem matrix_fiber_card {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) (z : I → Binary) :
    (Finset.univ.filter (fun y => A.mulVec y = z)).card ≤ 2 ^ (Fintype.card J - A.rank) := by
  classical
  have h := FiniteLinearLaw.fiber_card_le_kernel A.mulVecLin z
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hd
  have hk : Module.finrank Binary (LinearMap.ker A.mulVecLin) = Fintype.card J - A.rank := by
    change A.rank + Module.finrank Binary (LinearMap.ker A.mulVecLin) = Fintype.card J at hd
    omega
  have h' : (Finset.univ.filter (fun y => A.mulVec y = z)).card ≤ Fintype.card (LinearMap.ker A.mulVecLin) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Matrix.mulVecLin_apply] using h
  rw [FiniteLinearLaw.binary_card, hk] at h'
  exact h'

/--
---
conclusion: Lax342547.BilinearWalsh.correlation_sq
---
Group the second weight over the fibers of the matrix's linear map.
Fiberwise Cauchy-Schwarz costs at most 2^(number of columns - rank) in
squared energy. Apply the full dot-product Walsh bound to the resulting
weight on the row-coordinate space.
-/
theorem correlation_sq {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) :
    (correlation A f g) ^ 2 ≤ (2 : ℝ) ^ (Fintype.card I + (Fintype.card J - A.rank)) *
      (∑ x, (f x) ^ 2) * ∑ y, (g y) ^ 2 := by
  classical
  let w := pushWeight A.mulVec g
  have heq : correlation A f g = ∑ x, ∑ z, f x * w z * phase x z := by
    unfold correlation
    apply Finset.sum_congr rfl
    intro x _
    have h := pushWeight_sum A.mulVec g (fun z => f x * phase x z)
    simpa only [w, mul_right_comm] using h.symm
  rw [heq]
  have hw := pushWeight_energy A.mulVec g (2 ^ (Fintype.card J - A.rank)) (matrix_fiber_card A)
  calc
    _ ≤ (2 : ℝ) ^ Fintype.card I * (∑ x, (f x) ^ 2) * ∑ z, (w z) ^ 2 :=
      Walsh.dot_correlation_sq f w
    _ ≤ (2 : ℝ) ^ Fintype.card I * (∑ x, (f x) ^ 2) *
        ((2 : ℝ) ^ (Fintype.card J - A.rank) * ∑ y, (g y) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hw
      · positivity
    _ = _ := by rw [pow_add]; ring

theorem bounded_energy {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Binary) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∑ x, (f x) ^ 2 ≤ (2 : ℝ) ^ Fintype.card I := by
  calc
    _ ≤ ∑ _x : I → Binary, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      have h := abs_le.mp (hf x)
      nlinarith
    _ = _ := by simp [Binary]

/--
---
conclusion: Lax342547.BilinearWalsh.uniform_bound
---
Bound each weight's squared energy by the number of inputs. Rank-nullity
cancels the inactive coordinates after normalization, leaving squared
correlation at most 2^(-rank), hence the claimed square-root bound.
-/
theorem uniform_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |average A f g| ≤ 1 / Real.sqrt ((2 : ℝ) ^ A.rank) := by
  let C : ℝ := 2 ^ Fintype.card I * 2 ^ Fintype.card J
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : A.rank ≤ Fintype.card J := Matrix.rank_le_card_width A
  have hbound := (correlation_sq A f g).trans
    (show (2 : ℝ) ^ (Fintype.card I + (Fintype.card J - A.rank)) *
      (∑ x, (f x) ^ 2) * ∑ y, (g y) ^ 2 ≤
        (2 : ℝ) ^ (Fintype.card I + (Fintype.card J - A.rank)) *
          2 ^ Fintype.card I * 2 ^ Fintype.card J from by
      have h₁ := bounded_energy f hf
      have h₂ := bounded_energy g hg
      gcongr)
  have he : (2 : ℝ) ^ (Fintype.card I + (Fintype.card J - A.rank)) *
      2 ^ Fintype.card I * 2 ^ Fintype.card J * 2 ^ A.rank = C ^ 2 := by
    dsimp [C]
    simp only [← pow_add, ← pow_mul]
    congr 1
    omega
  have hmul : (correlation A f g) ^ 2 * (2 : ℝ) ^ A.rank ≤ C ^ 2 := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right hbound (by positivity)
  have hsq : (average A f g) ^ 2 ≤ 1 / (2 : ℝ) ^ A.rank := by
    change (correlation A f g / C) ^ 2 ≤ _
    rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hC) (by positivity)]
    simpa using hmul
  have h := Real.abs_le_sqrt hsq
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at h
  exact h

theorem average_scale {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) (c d : ℝ) :
    average A (fun x => c * f x) (fun y => d * g y) = c * d * average A f g := by
  have h : correlation A (fun x => c * f x) (fun y => d * g y) = c * d * correlation A f g := by
    simp only [correlation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  unfold average
  rw [h]
  ring

/--
---
conclusion: Lax342547.BilinearWalsh.bounded_weight_bound
---
Normalize both weights by their sup bounds and apply the uniform rank
estimate. If either bound is zero its weight vanishes identically.
-/
theorem bounded_weight_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hf : ∀ x, |f x| ≤ C₁) (hg : ∀ y, |g y| ≤ C₂) :
    |average A f g| ≤ C₁ * C₂ / Real.sqrt ((2 : ℝ) ^ A.rank) := by
  by_cases hz₁ : C₁ = 0
  · have hf₀ (x) : f x = 0 := abs_nonpos_iff.mp (hz₁ ▸ hf x)
    simp [average, correlation, hf₀, hz₁]
  by_cases hz₂ : C₂ = 0
  · have hg₀ (y) : g y = 0 := abs_nonpos_iff.mp (hz₂ ▸ hg y)
    simp [average, correlation, hg₀, hz₂]
  have hp₁ : 0 < C₁ := lt_of_le_of_ne hC₁ (Ne.symm hz₁)
  have hp₂ : 0 < C₂ := lt_of_le_of_ne hC₂ (Ne.symm hz₂)
  have hf' (x) : |f x / C₁| ≤ 1 := by
    rw [abs_div, abs_of_pos hp₁, div_le_iff₀ hp₁]
    simpa only [one_mul] using hf x
  have hg' (y) : |g y / C₂| ≤ 1 := by
    rw [abs_div, abs_of_pos hp₂, div_le_iff₀ hp₂]
    simpa only [one_mul] using hg y
  have he := average_scale A (fun x => f x / C₁) (fun y => g y / C₂) C₁ C₂
  have hfrec : (fun x => C₁ * (f x / C₁)) = f := by funext x; field_simp
  have hgrec : (fun y => C₂ * (g y / C₂)) = g := by funext y; field_simp
  rw [hfrec, hgrec] at he
  rw [he, abs_mul, abs_of_nonneg (mul_nonneg hC₁ hC₂)]
  calc
    _ ≤ C₁ * C₂ * (1 / Real.sqrt ((2 : ℝ) ^ A.rank)) :=
      mul_le_mul_of_nonneg_left (uniform_bound A _ _ hf' hg') (mul_nonneg hC₁ hC₂)
    _ = _ := by ring

/--
---
conclusion: Lax342547.BilinearWalsh.density_bound
---
Multiplying a bounded test weight by a nonnegative relative density
bounded by C multiplies its sup bound by at most C. The two factors
therefore cost C₁C₂, without changing the bilinear rank.
-/
theorem density_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (α f : (I → Binary) → ℝ) (β g : (J → Binary) → ℝ) (C₁ C₂ : ℝ)
    (hα : ∀ x, 0 ≤ α x ∧ α x ≤ C₁) (hβ : ∀ y, 0 ≤ β y ∧ β y ≤ C₂)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |average A (fun x => α x * f x) (fun y => β y * g y)| ≤
      C₁ * C₂ / Real.sqrt ((2 : ℝ) ^ A.rank) := by
  apply bounded_weight_bound A _ _ C₁ C₂ ((hα 0).1.trans (hα 0).2) ((hβ 0).1.trans (hβ 0).2)
  · intro x
    rw [abs_mul, abs_of_nonneg (hα x).1]
    exact (mul_le_mul_of_nonneg_left (hf x) (hα x).1).trans (by simpa using (hα x).2)
  · intro y
    rw [abs_mul, abs_of_nonneg (hβ y).1]
    exact (mul_le_mul_of_nonneg_left (hg y) (hβ y).1).trans (by simpa using (hβ y).2)

theorem abs_sign (z : Binary) : |sign z| = 1 := by
  rcases Walsh.binary_cases z with rfl | rfl <;> norm_num

/--
---
conclusion: Lax342547.BilinearWalsh.separate_phase_bound
---
An arbitrary phase depending only on one input group can be absorbed
into that group's weight without changing its absolute value. This
includes all affine terms and any frozen within-group quadratic phases.
-/
theorem separate_phase_bound {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary)
    (f : (I → Binary) → ℝ) (g : (J → Binary) → ℝ)
    (u : (I → Binary) → Binary) (v : (J → Binary) → Binary) (c : Binary)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |(∑ x, ∑ y, f x * g y * sign (dotProduct x (A.mulVec y) + u x + v y + c)) /
      ((2 : ℝ) ^ Fintype.card I * 2 ^ Fintype.card J)| ≤ 1 / Real.sqrt ((2 : ℝ) ^ A.rank) := by
  have h := uniform_bound A (fun x => f x * sign (u x + c)) (fun y => g y * sign (v y))
    (fun x => by simpa only [abs_mul, abs_sign, mul_one] using hf x)
    (fun y => by simpa only [abs_mul, abs_sign, mul_one] using hg y)
  have heq : (∑ x, ∑ y, f x * g y * sign (dotProduct x (A.mulVec y) + u x + v y + c)) =
      correlation A (fun x => f x * sign (u x + c)) (fun y => g y * sign (v y)) := by
    unfold correlation
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [Walsh.sign_add, phase]
    ring
  simpa only [average, heq] using h

/--
---
conclusion: Lax342547.BilinearWalsh.conditional_mixture_bound
---
Apply the bilinear estimate separately after each finite conditioning
record. The two coefficient spaces may depend on the record. Sum with
the original nonnegative cell masses, retaining all density costs and
without normalizing discarded mass away.
-/
theorem conditional_mixture_bound {T : Type} [Fintype T] {I J : T → Type}
    [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (I t)] [∀ t, DecidableEq (J t)]
    (A : ∀ t, Matrix (I t) (J t) Binary)
    (f : ∀ t, (I t → Binary) → ℝ) (g : ∀ t, (J t → Binary) → ℝ)
    (w C₁ C₂ : T → ℝ) (R : ℕ) (hw : ∀ t, 0 ≤ w t)
    (hC₁ : ∀ t, 0 ≤ C₁ t) (hC₂ : ∀ t, 0 ≤ C₂ t)
    (hf : ∀ t x, |f t x| ≤ C₁ t) (hg : ∀ t y, |g t y| ≤ C₂ t)
    (hR : ∀ t, R ≤ (A t).rank) :
    |∑ t, w t * average (A t) (f t) (g t)| ≤
      (∑ t, w t * C₁ t * C₂ t) / Real.sqrt ((2 : ℝ) ^ R) := by
  calc
    _ ≤ ∑ t, |w t * average (A t) (f t) (g t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, w t * (C₁ t * C₂ t / Real.sqrt ((2 : ℝ) ^ R)) := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul, abs_of_nonneg (hw t)]
      apply mul_le_mul_of_nonneg_left _ (hw t)
      refine (bounded_weight_bound (A t) (f t) (g t) (C₁ t) (C₂ t)
        (hC₁ t) (hC₂ t) (hf t) (hg t)).trans ?_
      have hpos := mul_nonneg (hC₁ t) (hC₂ t)
      have hr := hR t
      gcongr
      norm_num
    _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

end Lax342547Proofs.BilinearWalsh
