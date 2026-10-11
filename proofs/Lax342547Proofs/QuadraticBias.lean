import Lax342547.QuadraticBias
import Lax342547Proofs.Walsh
import Lax342547Proofs.FiniteLinearLaw
import Lax342547.RestrictionRank
import Lax342547.Walsh

namespace Lax342547Proofs.QuadraticBias
open Lax342547.QuadraticBias

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh
open scoped BigOperators

/--
---
conclusion: Lax342547.QuadraticBias.square_translation
---
-/
theorem square_translation {V : Type} [AddCommGroup V] [Fintype V]
    (f : V → ℝ) :
    (∑ x, f x)^2 = ∑ h, ∑ x, f x*f (x+h) := by
  classical
  rw [pow_two,Finset.sum_mul_sum]
  have ht (x : V) : (∑ y, f x*f y) = ∑ h, f x*f (x+h) := by
    exact Equiv.sum_comp (Equiv.addLeft x) (fun y => f x*f y) |>.symm
  simp only [ht]
  exact Finset.sum_comm

/--
---
conclusion: Lax342547.QuadraticBias.polar_sign_product
---
-/
theorem polar_sign_product {V : Type} [AddCommGroup V] [Module Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) (x h : V) :
    sign (Q x)*sign (Q (x+h)) = sign (Q h+Q 0)*sign (B h x) := by
  rw [← Lax342547Proofs.Walsh.sign_add,← Lax342547Proofs.Walsh.sign_add,← hpolar x h]
  congr 1
  have he (a : Binary) : a+a = 0 := by
    have hh : (2 : Binary) = 0 := rfl
    simpa only [two_mul,hh,zero_mul] using (two_mul a).symm
  calc
    Q x+Q (x+h) = (Q h+Q h)+(Q 0+Q 0)+(Q x+Q (x+h)) := by rw [he,he];simp
    _ = _ := by abel

/--
---
conclusion: Lax342547.QuadraticBias.quadratic_sign_square
---
-/
theorem quadratic_sign_square {V : Type} [AddCommGroup V] [Module Binary V] [Fintype V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) :
    by
      classical
      exact (∑ x, sign (Q x))^2 = (Fintype.card V : ℝ)*
      ∑ h ∈ Finset.univ.filter (fun h => B h = 0),sign (Q h+Q 0) := by
  classical
  rw [Lax342547.QuadraticBias.square_translation]
  simp only [Lax342547.QuadraticBias.polar_sign_product Q B hpolar,← Finset.mul_sum]
  have hh (h : V) : (∑ x, sign (B h x)) =
      if B h = 0 then (Fintype.card V : ℝ) else 0 := by
    by_cases hz : B h = 0
    · simp [hz,Lax342547Proofs.Walsh.sign_zero]
    · simp only [if_neg hz]
      exact Lax342547.Walsh.linear_orthogonality (B h) hz
  simp only [hh]
  rw [Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> ring

/--
---
conclusion: Lax342547.QuadraticBias.quadratic_bias_square_bound
---
-/
theorem quadratic_bias_square_bound {V : Type} [AddCommGroup V] [Module Binary V]
    [Fintype V] [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x) :
    ((∑ x, sign (Q x))/(Fintype.card V : ℝ))^2 ≤
      1/(2 : ℝ)^Module.finrank Binary (LinearMap.range B) := by
  classical
  have hs : (∑ h ∈ Finset.univ.filter (fun h => B h = 0),sign (Q h+Q 0)) ≤
      ((Finset.univ.filter (fun h => B h = 0)).card : ℝ) := by
    calc
      _ ≤ ∑ _h ∈ Finset.univ.filter (fun h => B h = 0),(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        unfold sign
        split_ifs <;> norm_num
      _ = _ := by simp
  have hk : (Finset.univ.filter (fun h => B h = 0)).card = Fintype.card (LinearMap.ker B) := by
    simp only [Fintype.card_subtype,LinearMap.mem_ker]
  have hmain : (∑ x, sign (Q x))^2 ≤ (Fintype.card V : ℝ)*(Fintype.card (LinearMap.ker B) : ℝ) := by
    rw [Lax342547.QuadraticBias.quadratic_sign_square Q B hpolar]
    rw [hk] at hs
    exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
  have hd := B.finrank_range_add_finrank_ker
  have hc : (Fintype.card V : ℝ) =
      (Fintype.card (LinearMap.ker B) : ℝ)*(2 : ℝ)^Module.finrank Binary (LinearMap.range B) := by
    rw [Lax342547Proofs.FiniteLinearLaw.binary_card V,
      Lax342547Proofs.FiniteLinearLaw.binary_card (LinearMap.ker B)]
    push_cast
    rw [← pow_add,add_comm,hd]
  have hv : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : 0 < (2 : ℝ)^Module.finrank Binary (LinearMap.range B) := by positivity
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hv 2)).mpr
  have he : (1/(2 : ℝ)^Module.finrank Binary (LinearMap.range B))*(Fintype.card V : ℝ)^2 =
      (Fintype.card V : ℝ)*(Fintype.card (LinearMap.ker B) : ℝ) := by
    rw [hc]
    field_simp
  rw [he]
  exact hmain

/--
---
conclusion: Lax342547.QuadraticBias.quadratic_bias_rank_bound
---
-/
theorem quadratic_bias_rank_bound {V : Type} [AddCommGroup V] [Module Binary V]
    [Fintype V] [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V) (r : ℕ)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (hrank : 2*r ≤ Module.finrank Binary (LinearMap.range B)) :
    |(∑ x, sign (Q x))/(Fintype.card V : ℝ)| ≤ 1/(2 : ℝ)^r := by
  have hs := Lax342547.QuadraticBias.quadratic_bias_square_bound Q B hpolar
  have hp : 1/(2 : ℝ)^Module.finrank Binary (LinearMap.range B) ≤ (1/(2 : ℝ)^r)^2 := by
    rw [div_pow,one_pow,← pow_mul]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by simpa only [mul_comm] using hrank))
  have hsq : |(∑ x, sign (Q x))/(Fintype.card V : ℝ)|^2 ≤ (1/(2 : ℝ)^r)^2 := by
    simpa only [sq_abs] using hs.trans hp
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq

/--
---
conclusion: Lax342547.QuadraticBias.affine_restricted_polar
---
-/
theorem affine_restricted_polar {V : Type} [AddCommGroup V] [Module Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (S : Submodule Binary V) (w : V) (x h : S) :
    Q (w+(x+h).val)+Q (w+x.val)+Q (w+h.val)+Q w = (B.restrict S) h x := by
  have he (a : Binary) : a+a = 0 := by
    have hh : (2 : Binary) = 0 := rfl
    simpa only [two_mul,hh,zero_mul] using (two_mul a).symm
  have ha := hpolar (w+x.val) h.val
  have hb := hpolar w h.val
  calc
    _ = (Q ((w+x.val)+h.val)+Q (w+x.val)+Q h.val+Q 0)+
        (Q (w+h.val)+Q w+Q h.val+Q 0) := by
      simp only [Submodule.coe_add,add_assoc]
      have hz : Q h.val+Q h.val+(Q 0+Q 0) = 0 := by rw [he,he];simp
      calc
        _ = _+0 := (add_zero _).symm
        _ = _+(Q h.val+Q h.val+(Q 0+Q 0)) := by rw [hz]
        _ = _ := by abel
    _ = B h.val (w+x.val)+B h.val w := by rw [ha,hb]
    _ = (B.restrict S) h x := by rw [map_add]; change _ = B h.val x.val; rw [add_assoc,add_comm (B h.val x.val),← add_assoc,he,zero_add]

/--
---
conclusion: Lax342547.QuadraticBias.affine_subspace_bias
---
-/
theorem affine_subspace_bias {V : Type} [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary V]
    (Q : V → Binary) (B : LinearMap.BilinForm Binary V) (S : Submodule Binary V) [Fintype S]
    (w : V) (r c : ℕ)
    (hpolar : ∀ x h, Q (x+h)+Q x+Q h+Q 0 = B h x)
    (hrank : 2*r ≤ Module.finrank Binary (LinearMap.range B))
    (hcodim : Module.finrank Binary V ≤ Module.finrank Binary S+c) :
    |(∑ x : S, sign (Q (w+x.val)))/(Fintype.card S : ℝ)| ≤ 1/(2 : ℝ)^(r-c) := by
  apply Lax342547.QuadraticBias.quadratic_bias_rank_bound (fun x : S => Q (w+x.val)) (B.restrict S) (r-c)
  · intro x h
    simpa only [Submodule.coe_zero,add_zero] using Lax342547.QuadraticBias.affine_restricted_polar Q B hpolar S w x h
  · have hl := Lax342547.RestrictionRank.bilinear_restriction_rank B S
    have hd := Submodule.finrank_le S
    omega

end Lax342547Proofs.QuadraticBias
