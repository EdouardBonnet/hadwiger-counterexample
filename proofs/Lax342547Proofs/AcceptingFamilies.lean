import Lax342547.AcceptingFamilies
import Lax342547.FiniteSampling
import Lax342547.RetainedImages

namespace Lax342547Proofs.AcceptingFamilies
open Lax342547.AcceptingFamilies

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.AcceptingFamilies.conditional_event_mass
---
-/
theorem conditional_event_mass {A : Type} [Fintype A] (α : A → ℝ) (C F : A → Prop) :
    cellMass (conditionalLaw α C) F = cellMass α (fun a => C a ∧ F a) / cellMass α C := by
  classical
  unfold cellMass conditionalLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : C a <;> by_cases hf : F a <;> simp [hc,hf,cellMass]

/--
---
conclusion: Lax342547.AcceptingFamilies.conditional_probability
---
-/
theorem conditional_probability {A : Type} [Fintype A] (α : A → ℝ) (C : A → Prop)
    (hα : Probability α) (hC : 0 < cellMass α C) : Probability (conditionalLaw α C) := by
  exact ⟨Lax342547.RetainedImages.conditional_law_nonneg α C hα.1,
    Lax342547.RetainedImages.conditional_law_total α C hC⟩

/--
---
conclusion: Lax342547.AcceptingFamilies.accepting_family_loss
---
-/
theorem accepting_family_loss {A B I : Type} [Fintype A] [Fintype B] [Fintype I]
    (α : A → ℝ) (β : B → ℝ) (C : I → A → Prop) (key : B → I) (F : B → A → Prop)
    (η τ U : ℝ) (hα : Probability α) (hβ : Probability β)
    (hη : 0 ≤ η) (hτ : 0 < τ) (hU : 0 ≤ U)
    (hex : ∀ i, τ ≤ cellMass α (C i) →
      cellMass β (fun b => η ≤ cellMass (conditionalLaw α (C i)) (F b)) ≤ U) :
    (∑ b, β b * cellMass α (fun a => C (key b) a ∧ F b a)) ≤
      η * (∑ b, β b * cellMass α (C (key b))) + τ + Fintype.card I * U := by
  classical
  let bad := fun b => ∃ i,τ ≤ cellMass α (C i) ∧
    η ≤ cellMass (conditionalLaw α (C i)) (F b)
  have hmass (P : A → Prop) : 0 ≤ cellMass α P := by
    unfold cellMass
    exact Finset.sum_nonneg (fun a _ => by split_ifs; exact hα.1 a; exact le_rfl)
  have hone (P : A → Prop) : cellMass α P ≤ 1 := by
    have hh := Lax342547.FiniteSampling.cell_mass_mono α P (fun _ => True) hα.1 (fun _ _ => trivial)
    simpa [cellMass,hα.2] using hh
  have hbadi (i : I) : cellMass β (fun b => τ ≤ cellMass α (C i) ∧
      η ≤ cellMass (conditionalLaw α (C i)) (F b)) ≤ U := by
    by_cases hi : τ ≤ cellMass α (C i)
    · simpa only [hi,true_and] using hex i hi
    · simp only [hi,false_and]
      simpa [cellMass] using hU
  have hbad : cellMass β bad ≤ Fintype.card I * U := by
    have hu := Lax342547.FiniteSampling.cell_mass_union_bound β
      (fun i b => τ ≤ cellMass α (C i) ∧ η ≤ cellMass (conditionalLaw α (C i)) (F b))
      Finset.univ hβ.1
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbadi i)
    have hh := hu.trans hs
    simpa [bad] using hh
  have hpoint (b : B) : cellMass α (fun a => C (key b) a ∧ F b a) ≤
      η*cellMass α (C (key b)) + τ + if bad b then 1 else 0 := by
    have hm := Lax342547.FiniteSampling.cell_mass_mono α
      (fun a => C (key b) a ∧ F b a) (C (key b)) hα.1 (fun _ h => h.1)
    have hnon : 0 ≤ η*cellMass α (C (key b)) := mul_nonneg hη (hmass _)
    by_cases hb : bad b
    · rw [if_pos hb]
      have hh := hone (fun a => C (key b) a ∧ F b a)
      linarith
    · rw [if_neg hb]
      by_cases hc : τ ≤ cellMass α (C (key b))
      · have hg : cellMass (conditionalLaw α (C (key b))) (F b) < η := by
          by_contra! hn
          exact hb ⟨key b,hc,hn⟩
        rw [Lax342547.AcceptingFamilies.conditional_event_mass] at hg
        have ht := (div_lt_iff₀ (lt_of_lt_of_le hτ hc)).mp hg
        linarith
      · have hh : cellMass α (C (key b)) < τ := lt_of_not_ge hc
        linarith
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpoint b) (hβ.1 b))
  have he : (∑ b,β b * (η*cellMass α (C (key b)) + τ + if bad b then 1 else 0)) =
      η*(∑ b,β b*cellMass α (C (key b))) + τ + cellMass β bad := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    have h₁ : (∑ b,β b*(η*cellMass α (C (key b)))) = η*(∑ b,β b*cellMass α (C (key b))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have h₂ : (∑ b,β b*τ) = τ := by rw [← Finset.sum_mul,hβ.2,one_mul]
    have h₃ : (∑ b,β b*(if bad b then 1 else 0)) = cellMass β bad := by
      unfold cellMass
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    rw [h₁,h₂,h₃]
  exact (hs.trans_eq he).trans (add_le_add_right hbad _)

end Lax342547Proofs.AcceptingFamilies
