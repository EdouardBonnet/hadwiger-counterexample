import Lax342547.BooleanWeight
import Lax342547Proofs.SelectorInterpolation
import Lax342547Proofs.Walsh
import Lax342547Proofs.FiniteSampling

namespace Lax342547Proofs.BooleanWeight
open Lax342547.BooleanWeight

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

/--
---
conclusion: Lax342547.BooleanWeight.flip_twice
---
-/
theorem flip_twice {b : ℕ} (i : Fin b) (x : Fin b → Binary) : Lax342547.BooleanWeight.flip i (Lax342547.BooleanWeight.flip i x) = x := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [Lax342547.BooleanWeight.flip,Function.update,ZModModule.add_self,add_assoc]
  · simp [Lax342547.BooleanWeight.flip,hj]

/--
---
conclusion: Lax342547.BooleanWeight.derivative_monomial
---
-/
theorem derivative_monomial {b : ℕ} (i : Fin b) (S : Finset (Fin b)) :
    derivative i (monomial S) = if i ∈ S then monomial (S.erase i) else 0 := by
  classical
  ext x
  by_cases hi : i ∈ S
  · simp only [hi,ite_true,derivative]
    rw [monomial,← Finset.mul_prod_erase S x hi]
    have he : monomial S (Lax342547.BooleanWeight.flip i x) = (x i+1)*monomial (S.erase i) x := by
      unfold monomial
      rw [← Finset.mul_prod_erase S (Lax342547.BooleanWeight.flip i x) hi]
      simp only [Lax342547.BooleanWeight.flip,Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [he]
    change x i*monomial (S.erase i) x+(x i+1)*monomial (S.erase i) x = _
    rw [← add_mul]
    simp [ZModModule.add_self,add_assoc,← add_assoc]
  · simp only [hi,ite_false,Pi.zero_apply,derivative]
    have he : monomial S (Lax342547.BooleanWeight.flip i x) = monomial S x := by
      unfold monomial
      apply Finset.prod_congr rfl
      intro j hj
      apply Function.update_of_ne
      exact fun he => hi (he ▸ hj)
    rw [he,ZModModule.add_self]

/--
---
conclusion: Lax342547.BooleanWeight.derivative_degree
---
-/
theorem derivative_degree {b d : ℕ} (i : Fin b) (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b (d+1)) : derivative i f ∈ selectorSpan b d := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S,hS,rfl⟩ := hf
    rw [derivative_monomial]
    split_ifs with hi
    · exact Lax342547Proofs.SelectorInterpolation.monomial_mem _ (by
        have he := Finset.card_erase_of_mem hi
        omega)
    · exact Submodule.zero_mem _
  | zero =>
    have he : derivative i (0 : (Fin b → Binary) → Binary) = 0 := by ext x; simp [derivative]
    rw [he]
    exact (selectorSpan b d).zero_mem
  | add f g _ _ hf hg =>
    have he : derivative i (f+g) = derivative i f+derivative i g := by ext x; simp [derivative]; ring
    rw [he]
    exact (selectorSpan b d).add_mem hf hg
  | smul c f _ hf =>
    have he : derivative i (c • f) = c • derivative i f := by ext x; simp [derivative,smul_eq_mul,mul_add]
    rw [he]
    exact (selectorSpan b d).smul_mem c hf

/--
---
conclusion: Lax342547.BooleanWeight.invariant_constant
---
-/
theorem invariant_constant {b : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : ∀ i x, f (Lax342547.BooleanWeight.flip i x) = f x) : ∀ x y, f x = f y := by
  classical
  have hu (i : Fin b) (x : Fin b → Binary) (v : Binary) : f (Function.update x i v) = f x := by
    by_cases hv : v = x i
    · rw [hv,Function.update_eq_self]
    · have he : v = x i+1 := by
        generalize x i = a at hv ⊢
        fin_cases v <;> fin_cases a <;> first | rfl | exact False.elim (hv rfl)
      rw [he]
      exact hf i x
  have hall : ∀ S : Finset (Fin b), ∀ x y : Fin b → Binary,
      (∀ i, i ∉ S → x i = y i) → f x = f y := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x y hxy
      have he : x = y := funext (fun i => hxy i (by simp))
      rw [he]
    | @insert i S hi ih =>
      intro x y hxy
      have hh : f (Function.update x i (y i)) = f y := by
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · rw [Function.update_of_ne hji]
          exact hxy j (by simp [hj,hji])
      exact (hu i x (y i)).symm.trans hh
  intro x y
  exact hall Finset.univ x y (by simp)

/--
---
conclusion: Lax342547.BooleanWeight.derivative_weight
---
-/
theorem derivative_weight {b : ℕ} (i : Fin b) (f : (Fin b → Binary) → Binary) :
    weight (derivative i f) ≤ 2*weight f := by
  classical
  let e : (Fin b → Binary) ≃ (Fin b → Binary) := {
    toFun := Lax342547.BooleanWeight.flip i
    invFun := Lax342547.BooleanWeight.flip i
    left_inv := flip_twice i
    right_inv := flip_twice i }
  have hs : weight f = ∑ x : Fin b → Binary, if f x ≠ 0 then 1 else 0 := by
    simp [weight,Finset.card_filter]
  have hd : weight (derivative i f) ≤
      (∑ x : Fin b → Binary, if f x ≠ 0 then 1 else 0)+
        (∑ x : Fin b → Binary, if f (Lax342547.BooleanWeight.flip i x) ≠ 0 then 1 else 0) := by
    simp only [weight,Finset.card_filter,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : f x = 0 <;> by_cases hy : f (Lax342547.BooleanWeight.flip i x) = 0 <;> simp [derivative,hx,hy] <;> split_ifs <;> omega
  have he : (∑ x : Fin b → Binary, if f (Lax342547.BooleanWeight.flip i x) ≠ 0 then 1 else 0) = weight f := by
    rw [hs]
    exact e.sum_comp (fun x => if f x ≠ 0 then 1 else 0)
  rw [← hs,he] at hd
  omega

/--
---
conclusion: Lax342547.BooleanWeight.constant_weight
---
-/
theorem constant_weight {b : ℕ} (c : Binary) (hc : c ≠ 0) :
    weight (fun _ : Fin b → Binary => c) = 2^b := by
  simp [weight,hc,Fintype.card_fun,ZMod.card]

/--
---
conclusion: Lax342547.BooleanWeight.nonzero_weight
---
-/
theorem nonzero_weight {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (hne : f ≠ 0) : 2^b ≤ 2^d*weight f := by
  classical
  induction d generalizing f with
  | zero =>
    have hconst : ∃ c : Binary, f = fun _ => c := by
      clear hne
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨S,hS,rfl⟩ := hf
        have he : S = ∅ := Finset.card_eq_zero.mp (by omega)
        exact ⟨1,by simp [he,monomial]; rfl⟩
      | zero => exact ⟨0,rfl⟩
      | add f g _ _ hf hg =>
        obtain ⟨c,rfl⟩ := hf
        obtain ⟨e,rfl⟩ := hg
        exact ⟨c+e,rfl⟩
      | smul c f _ hf =>
        obtain ⟨e,rfl⟩ := hf
        exact ⟨c*e,rfl⟩
    obtain ⟨c,rfl⟩ := hconst
    have hc : c ≠ 0 := by intro hc; exact hne (by rw [hc]; rfl)
    simp [constant_weight c hc]
  | succ d ih =>
    by_cases hd : ∃ i, derivative i f ≠ 0
    · obtain ⟨i,hi⟩ := hd
      have hh := ih (derivative i f) (derivative_degree i f hf) hi
      have hw := derivative_weight i f
      calc
        _ ≤ 2^d*weight (derivative i f) := hh
        _ ≤ 2^d*(2*weight f) := Nat.mul_le_mul_left _ hw
        _ = _ := by rw [pow_succ]; ring
    · have hsame : ∀ i x, f (Lax342547.BooleanWeight.flip i x) = f x := by
        intro i x
        have hder : derivative i f = 0 := by simpa only [not_not] using (not_exists.mp hd i)
        have he := congrFun hder x
        change f x+f (Lax342547.BooleanWeight.flip i x) = 0 at he
        have hs : f x+f x = 0 := ZModModule.add_self _
        exact add_left_cancel (he.trans hs.symm)
      have he : f = fun _ => f 0 := funext (fun x => invariant_constant f hsame x 0)
      rw [he] at hne ⊢
      have hc : f 0 ≠ 0 := by intro hc; exact hne (by rw [hc]; rfl)
      rw [constant_weight _ hc]
      exact Nat.le_mul_of_pos_left _ (by positivity)

/--
---
conclusion: Lax342547.BooleanWeight.uniform_nonzero_mass
---
-/
theorem uniform_nonzero_mass {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (hne : f ≠ 0) :
    1/(2 : ℝ)^d ≤ Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) := by
  classical
  have he : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) = (weight f : ℝ)/(2 : ℝ)^b := by
    unfold Lax342547.RetainedImages.cellMass
    dsimp only
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => f x ≠ 0), 1/(2 : ℝ)^b := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = 0 <;> simp [hx]
      _ = _ := by simp [weight,div_eq_mul_inv]
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using
    (show ((2^b : ℕ) : ℝ) ≤ ((2^d*weight f : ℕ) : ℝ) from by exact_mod_cast nonzero_weight f hf hne)

/--
---
conclusion: Lax342547.BooleanWeight.uniform_error_exactification
---
-/
theorem uniform_error_exactification {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d)
    (herr : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) < 1/(2 : ℝ)^d) : f = 0 := by
  by_contra hn
  exact (not_lt_of_ge (uniform_nonzero_mass f hf hn)) herr

/--
---
conclusion: Lax342547.BooleanWeight.excluded_labels_exactification
---
-/
theorem excluded_labels_exactification {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (E : Finset (Fin b → Binary))
    (hzero : ∀ x, x ∉ E → f x = 0) (hE : 2^d*E.card < 2^b) : f = 0 := by
  classical
  by_contra hn
  have hw : weight f ≤ E.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hx
    exact not_not.mp (fun he => hx (hzero x he))
  have hh := nonzero_weight f hf hn
  have hm := Nat.mul_le_mul_left (2^d) hw
  omega

end Lax342547Proofs.BooleanWeight
