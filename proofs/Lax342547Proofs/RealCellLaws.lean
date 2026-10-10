import Lax342547.RealCellLaws
import Lax342547Proofs.RetainedImages
import Lax342547Proofs.Conditioning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Lax342547Proofs.RealCellLaws
open Lax342547.RealCellLaws

set_option backward.isDefEq.respectTransparency false
open Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped ENNReal

/--
---
conclusion: Lax342547.RealCellLaws.weights_nonneg
---
-/
theorem weights_nonneg {Ω : Type} (p : PMF Ω) (ω : Ω) : 0 ≤ weights p ω := by
  exact ENNReal.toReal_nonneg

/--
---
conclusion: Lax342547.RealCellLaws.weights_total
---
-/
theorem weights_total {Ω : Type} [Fintype Ω] (p : PMF Ω) : ∑ ω, weights p ω = 1 := by
  have h : ∑ ω, p ω = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  unfold weights
  rw [← ENNReal.toReal_sum (fun ω _ => p.apply_ne_top ω), h]
  rfl

/--
---
conclusion: Lax342547.RealCellLaws.event_mass
---
-/
theorem event_mass {Ω : Type} [Fintype Ω] (p : PMF Ω) (C : Ω → Prop) :
    cellMass (weights p) C = (p.toOuterMeasure {ω | C ω}).toReal := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [ENNReal.toReal_sum (fun ω _ => by split_ifs; exact p.apply_ne_top ω; exact ENNReal.zero_ne_top)]
  unfold cellMass weights
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> rfl

/--
---
conclusion: Lax342547.RealCellLaws.subtype_integral
---
-/
theorem subtype_integral {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (f : Ω → ℝ) : by
      classical
      exact (∑ ω : {ω // C ω}, subtypeWeights ρ C ω * f ω.val) =
        ∑ ω, conditionalLaw ρ C ω * f ω := by
  classical
  have hs := Finset.sum_subtype (F := inferInstance) (p := C) (Finset.univ.filter C)
    (by simp) (fun ω => ρ ω / cellMass ρ C * f ω)
  rw [Finset.sum_filter] at hs
  unfold subtypeWeights
  rw [← hs]
  apply Finset.sum_congr rfl
  intro ω _
  unfold conditionalLaw
  by_cases hω : C ω <;> simp [hω]

/--
---
conclusion: Lax342547.RealCellLaws.subtype_weights_total
---
-/
theorem subtype_weights_total {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hC : 0 < cellMass ρ C) : by
      classical
      exact (∑ ω : {ω // C ω}, subtypeWeights ρ C ω) = 1 := by
  classical
  have h := subtype_integral ρ C (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  exact Lax342547Proofs.RetainedImages.conditional_law_total ρ C hC

/--
---
conclusion: Lax342547.RealCellLaws.subtype_weights_nonneg
---
-/
theorem subtype_weights_nonneg {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (hρ : ∀ ω, 0 ≤ ρ ω) (hC : 0 < cellMass ρ C)
    (ω : {ω // C ω}) : 0 ≤ subtypeWeights ρ C ω := by
  exact div_nonneg (hρ ω.val) hC.le

/--
---
conclusion: Lax342547.RealCellLaws.subtype_image_push
---
-/
theorem subtype_image_push {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (x : X) : by
      classical
      exact push (subtypeWeights ρ C) (fun ω => image ω.val) x = push (conditionalLaw ρ C) image x := by
  classical
  have h := subtype_integral ρ C (fun ω => if image ω = x then 1 else 0)
  unfold push
  simpa only [mul_ite, mul_one, mul_zero] using h

/--
---
conclusion: Lax342547.RealCellLaws.subtype_conditional_cap
---
-/
theorem subtype_conditional_cap {Ω X : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ cap : ℝ) (hρ : ∀ ω, 0 ≤ ρ ω) (hτ : 0 < τ)
    (hC : τ ≤ cellMass ρ C) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, cellMass ρ (fun ω => joint ω ∧ image ω = x) ≤ cap) (x : X) : by
      classical
      exact push (subtypeWeights ρ C) (fun ω => image ω.val) x ≤ cap / τ := by
  classical
  rw [subtype_image_push]
  exact Lax342547Proofs.RetainedImages.conditional_image_cap ρ C image joint τ cap hρ hτ hC hCJ hcap x

/--
---
conclusion: Lax342547.RealCellLaws.pmf_subtype_conditional_cap
---
-/
theorem pmf_subtype_conditional_cap {Ω X : Type} [Fintype Ω]
    (p : PMF Ω) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (τ : ℝ) (cap : ℝ≥0∞) (hcapTop : cap ≠ ⊤) (hτ : 0 < τ)
    (hC : τ ≤ (p.toOuterMeasure {ω | C ω}).toReal) (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, p.toOuterMeasure {ω | joint ω ∧ image ω = x} ≤ cap) (x : X) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => image ω.val) x ≤ cap.toReal / τ := by
  classical
  apply subtype_conditional_cap (weights p) C image joint τ cap.toReal (weights_nonneg p) hτ
  · rwa [event_mass]
  · exact hCJ
  · intro y
    rw [event_mass]
    exact ENNReal.toReal_mono hcapTop (hcap y)

/--
---
conclusion: Lax342547.RealCellLaws.pmf_paper_subtype_cap
---
-/
theorem pmf_paper_subtype_cap {Ω X : Type} [Fintype Ω]
    (p : PMF Ω) (C : Ω → Prop) (image : Ω → X) (joint : Ω → Prop)
    (ζ k t N : ℝ) (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1 / 1000)
    (hk : 2 * ζ * k ≤ 1 / 500) (ht : 1 ≤ t) (hN : 0 ≤ N)
    (hC : (2 : ℝ) ^ (-(k + 1 / 100) * N) ≤ (p.toOuterMeasure {ω | C ω}).toReal)
    (hCJ : ∀ ω, C ω → joint ω)
    (hcap : ∀ x, p.toOuterMeasure {ω | joint ω ∧ image ω = x} ≤
      (2 : ℝ≥0∞) ^ (-(1 - 2 * ζ) * (k + t) * N)) (x : X) : by
      classical
      exact push (subtypeWeights (weights p) C) (fun ω => image ω.val) x ≤
        (2 : ℝ) ^ (-(95 / 100 : ℝ) * t * N) := by
  classical
  have hp := pmf_subtype_conditional_cap p C image joint
    ((2 : ℝ) ^ (-(k + 1 / 100) * N))
    ((2 : ℝ≥0∞) ^ (-(1 - 2 * ζ) * (k + t) * N))
    (by simp) (Real.rpow_pos_of_pos (by norm_num) _) hC hCJ hcap x
  rw [← ENNReal.toReal_rpow] at hp
  norm_num only [ENNReal.toReal_ofNat] at hp
  exact hp.trans (Lax342547Proofs.RetainedImages.paper_conditional_cap ζ k t N hζ hζsmall hk ht hN)

end Lax342547Proofs.RealCellLaws
