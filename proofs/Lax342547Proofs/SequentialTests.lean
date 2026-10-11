import Lax342547.SequentialTests
import Lax342547Proofs.FiniteSampling
import Mathlib.Data.Fin.Tuple.Basic

namespace Lax342547Proofs.SequentialTests
open Lax342547.SequentialTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.SequentialTests.step_probability
---
-/
theorem step_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (n : ℕ) :
    by
      classical
      exact cellMass (productLaw (fun _ : Fin (n+1) => μ)) (accepts P (n+1)) =
      ∑ s : Fin n → Ω,productLaw (fun _ : Fin n => μ) s*
        (if accepts P n s then cellMass μ (P n s) else 0) := by
  classical
  unfold cellMass
  let E := Fin.snocEquiv (fun _ : Fin (n+1) => Ω)
  have he := E.sum_comp (fun s => if accepts P (n+1) s then productLaw (fun _ : Fin (n+1) => μ) s else 0)
  rw [← he,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hprod (x : Ω) : productLaw (fun _ : Fin (n+1) => μ) (Fin.snoc s x) =
      productLaw (fun _ : Fin n => μ) s*μ x := by
    unfold productLaw
    rw [Fin.prod_univ_castSucc]
    simp
  by_cases hs : accepts P n s
  · simp only [hs,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [E,Fin.snocEquiv,Equiv.coe_fn_mk,accepts,Fin.init_snoc,Fin.snoc_last]
    rw [hprod]
    by_cases hx : P n s x <;> simp [hs,hx]
  · simp [E,Fin.snocEquiv,accepts,hs]

/--
---
conclusion: Lax342547.SequentialTests.sequential_lower_probability
---
-/
theorem sequential_lower_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (c : ℝ)
    (hμ : Probability μ) (hc : 0 ≤ c)
    (hstep : ∀ j s,accepts P j s → c ≤ cellMass μ (P j s)) (n : ℕ) :
    c^n ≤ cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n) := by
  classical
  induction n with
  | zero => simp [accepts,cellMass,productLaw]
  | succ n ih =>
    rw [step_probability]
    have hρ := Lax342547Proofs.FiniteSampling.product_probability (fun _ : Fin n => μ) (fun _ => hμ)
    have hs : c*cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n) ≤
        ∑ s : Fin n → Ω,productLaw (fun _ : Fin n => μ) s*
          (if accepts P n s then cellMass μ (P n s) else 0) := by
      unfold cellMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      by_cases h : accepts P n s
      · simp only [h,ite_true]
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left (hstep n s h) (hρ.1 s)
      · simp [h]
    simpa only [pow_succ,mul_comm c] using (mul_le_mul_of_nonneg_left ih hc).trans hs

/--
---
conclusion: Lax342547.SequentialTests.bounded_sequential_lower_probability
---
-/
theorem bounded_sequential_lower_probability {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (P : ∀ j,(Fin j → Ω) → Ω → Prop) (c : ℝ)
    (hμ : Probability μ) (hc : 0 ≤ c)
    (n : ℕ) (hstep : ∀ j,j < n → ∀ s,accepts P j s → c ≤ cellMass μ (P j s)) :
    c^n ≤ cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n) := by
  classical
  revert hstep
  induction n with
  | zero => intro hstep; simp [accepts,cellMass,productLaw]
  | succ n ih =>
    intro hstep
    have ih' := ih (fun j hj s hs => hstep j (by omega) s hs)
    rw [step_probability]
    have hρ := Lax342547Proofs.FiniteSampling.product_probability (fun _ : Fin n => μ) (fun _ => hμ)
    have hs : c*cellMass (productLaw (fun _ : Fin n => μ)) (accepts P n) ≤
        ∑ s : Fin n → Ω,productLaw (fun _ : Fin n => μ) s*
          (if accepts P n s then cellMass μ (P n s) else 0) := by
      unfold cellMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      by_cases h : accepts P n s
      · simp only [h,ite_true]
        rw [mul_comm c]
        exact mul_le_mul_of_nonneg_left (hstep n (by omega) s h) (hρ.1 s)
      · simp [h]
    simpa only [pow_succ,mul_comm c] using (mul_le_mul_of_nonneg_left ih' hc).trans hs

/--
---
conclusion: Lax342547.SequentialTests.safe_failure_mass
---
-/
theorem safe_failure_mass {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F S : Ω → Prop) (hμ : ∀ x,0 ≤ μ x) :
    cellMass μ F-cellMass μ (fun x => ¬ S x) ≤ cellMass μ (fun x => F x ∧ S x) := by
  classical
  have hs : cellMass μ F ≤ cellMass μ (fun x => F x ∧ S x)+cellMass μ (fun x => ¬ S x) := by
    unfold cellMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hf : F x <;> by_cases hS : S x <;> simp [hf,hS,hμ x]
  linarith

/--
---
conclusion: Lax342547.SequentialTests.sequential_failure_lower
---
-/
theorem sequential_failure_lower {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F : Ω → Prop) (S : ∀ j,(Fin j → Ω) → Ω → Prop) (η δ : ℝ)
    (hμ : Probability μ) (hgap : δ ≤ η) (hF : η ≤ cellMass μ F)
    (havoid : ∀ j s,accepts (fun j s x => F x ∧ S j s x) j s →
      cellMass μ (fun x => ¬ S j s x) ≤ δ) (n : ℕ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (accepts (fun j s x => F x ∧ S j s x) n) := by
  apply sequential_lower_probability μ _ (η-δ) hμ (sub_nonneg.mpr hgap)
  intro j s hs
  have hh := safe_failure_mass μ F (S j s) hμ.1
  have hb := havoid j s hs
  linarith

/--
---
conclusion: Lax342547.SequentialTests.bounded_sequential_failure_lower
---
-/
theorem bounded_sequential_failure_lower {Ω : Type} [Fintype Ω] (μ : Ω → ℝ)
    (F : Ω → Prop) (S : ∀ j,(Fin j → Ω) → Ω → Prop) (η δ : ℝ)
    (hμ : Probability μ) (hgap : δ ≤ η) (hF : η ≤ cellMass μ F)
    (n : ℕ) (havoid : ∀ j,j < n → ∀ s,accepts (fun j s x => F x ∧ S j s x) j s →
      cellMass μ (fun x => ¬ S j s x) ≤ δ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (accepts (fun j s x => F x ∧ S j s x) n) := by
  apply bounded_sequential_lower_probability μ _ (η-δ) hμ (sub_nonneg.mpr hgap) n
  intro j hj s hs
  have hh := safe_failure_mass μ F (S j s) hμ.1
  have hb := havoid j hj s hs
  linarith

/--
---
conclusion: Lax342547.SequentialTests.accepts_pointwise
---
-/
theorem accepts_pointwise {Ω : Type} (P : ∀ j,(Fin j → Ω) → Ω → Prop) (F : Ω → Prop)
    (hP : ∀ j t x,P j t x → F x) (n : ℕ) (s : Fin n → Ω)
    (hs : accepts P n s) : ∀ i,F (s i) := by
  induction n with
  | zero => intro i;exact Fin.elim0 i
  | succ n ih =>
    change accepts P n (Fin.init s) ∧ P n (Fin.init s) (s (Fin.last n)) at hs
    have hi := ih (Fin.init s) hs.1
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hP n (Fin.init s) _ hs.2
    · exact hi j

end Lax342547Proofs.SequentialTests
