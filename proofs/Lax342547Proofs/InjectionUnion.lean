import Lax342547.InjectionUnion
import Lax342547.FiniteSampling
import Lax342547.InjectionAsymptotics

namespace Lax342547Proofs.InjectionUnion
open Lax342547.InjectionUnion

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.InjectionUnion.pair_event_mass
---
-/
theorem pair_event_mass {A B : Type} [Fintype A] [Fintype B] (α : A → ℝ) (β : B → ℝ)
    (E : A → B → Prop) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => E p.1 p.2) =
      ∑ b,β b*cellMass α (fun a => E a b) := by
  classical
  unfold cellMass
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : E a b <;> simp [he,mul_comm]

/--
---
conclusion: Lax342547.InjectionUnion.finite_injection_union
---
-/
theorem finite_injection_union {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    (α : A → ℝ) (β : B → ℝ) (accept : A → B → Prop) (F : J → A → B → Prop)
    (η τ : ℝ) (hα : ∀ a,0 ≤ α a) (hβ : ∀ b,0 ≤ β b)
    (hF : ∀ j,(∑ b,β b*cellMass α (fun a => accept a b ∧ F j a b)) ≤
      η*(∑ b,β b*cellMass α (fun a => accept a b))+τ) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2 ∧ ∃ j,F j p.1 p.2) ≤
      Fintype.card J*(η*cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2)+τ) := by
  classical
  have hu := Lax342547.FiniteSampling.cell_mass_union_bound
    (fun p : A × B => α p.1*β p.2)
    (fun j p => accept p.1 p.2 ∧ F j p.1 p.2) Finset.univ (fun p => mul_nonneg (hα p.1) (hβ p.2))
  have he : (fun p : A × B => ∃ j ∈ (Finset.univ : Finset J),accept p.1 p.2 ∧ F j p.1 p.2) =
      (fun p : A × B => accept p.1 p.2 ∧ ∃ j,F j p.1 p.2) := by
    ext p
    simp only [Finset.mem_univ,true_and,exists_and_left]
  rw [he] at hu
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hF j)
  simp_rw [← Lax342547.InjectionUnion.pair_event_mass] at hs
  exact hu.trans (by simpa [mul_add] using hs)

/--
---
conclusion: Lax342547.InjectionUnion.inverse_polynomial_relative_union
---
-/
theorem inverse_polynomial_relative_union {A B J : Type} [Fintype A] [Fintype B] [Fintype J]
    (α : A → ℝ) (β : B → ℝ) (accept : A → B → Prop) (F : J → A → B → Prop)
    (N c : ℕ) (ε : ℝ) (hJ : 0 < Fintype.card J) (hε : 0 ≤ ε)
    (hα : ∀ a,0 ≤ α a) (hβ : ∀ b,0 ≤ β b)
    (haccept : 1/(N : ℝ)^c ≤ cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2))
    (hF : ∀ j,(∑ b,β b*cellMass α (fun a => accept a b ∧ F j a b)) ≤
      (ε/(2*Fintype.card J))*(∑ b,β b*cellMass α (fun a => accept a b))+
        (1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N))
    (htail : (Fintype.card J : ℝ)*(1/(2 : ℝ)^(N/100)+1/(2 : ℝ)^N) ≤ (ε/2)/(N : ℝ)^c) :
    cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2 ∧ ∃ j,F j p.1 p.2) ≤
      ε*cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2) := by
  have ha : 0 ≤ cellMass (fun p : A × B => α p.1*β p.2) (fun p => accept p.1 p.2) := by
    classical
    unfold cellMass
    exact Finset.sum_nonneg (fun p _ => by split_ifs; exact mul_nonneg (hα p.1) (hβ p.2); exact le_rfl)
  apply Lax342547.InjectionAsymptotics.relative_union_budget (Fintype.card J) ε _ _ _ hJ hε ha
    (Lax342547.InjectionUnion.finite_injection_union α β accept F _ _ hα hβ hF)
  exact htail.trans (by simpa only [div_eq_mul_inv,one_div,one_mul] using
    mul_le_mul_of_nonneg_left haccept (by positivity : (0 : ℝ) ≤ ε/2))

end Lax342547Proofs.InjectionUnion
