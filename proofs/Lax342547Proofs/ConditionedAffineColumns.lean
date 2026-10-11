import Lax342547.ConditionedAffineColumns
import Lax342547Proofs.AffineSliceIndependence
import Lax342547Proofs.RealCellLaws

namespace Lax342547Proofs.ConditionedAffineColumns
noncomputable section
open Lax342547.ConditionedAffineColumns
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false


/--
---
conclusion: Lax342547.ConditionedAffineColumns.freePair_uniform
---
-/
theorem freePair_uniform {k n : ℕ} {D : Type} [Fintype D] [DecidableEq D] :
    (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)).map
      (freePairMap (k := k) (n := n) (D := D)) =
      PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary) := by
  classical
  apply FiniteLinearLaw.uniform_image_of_surjective
  intro Z
  refine ⟨(setFree 0 Z.1,setFree 0 Z.2),?_⟩
  change (freePart (setFree 0 Z.1),freePart (setFree 0 Z.2)) = Z
  simp

/--
---
conclusion: Lax342547.ConditionedAffineColumns.nominal_pair_failure
---
-/
theorem nominal_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) :
    (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)).toOuterMeasure
      {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s V.1).mulVec uv.1+
          (pointColumns (degree := degree) s V.2).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n := by
  classical
  let p := PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)
  have he : p.toOuterMeasure {V | ¬ Function.Injective (joinedFree (freePart V.1,freePart V.2)).mulVec} =
      (PMF.uniformOfFintype (Matrix (Fin n) (Option (D ⊕ D)) Binary)).toOuterMeasure
        {Z | ¬ Function.Injective Z.mulVec} := by
    have hu := congrArg (fun q => q.map joinedFree) (freePair_uniform (k := k) (n := n) (D := D))
    rw [PMF.map_comp,AffineSliceIndependence.joinedFree_uniform] at hu
    have ht := congrArg (fun q => q.toOuterMeasure {Z | ¬ Function.Injective Z.mulVec}) hu
    rw [PMF.toOuterMeasure_map_apply] at ht
    exact ht
  have hsub : {V : Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary |
      ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s V.1).mulVec uv.1+
          (pointColumns (degree := degree) s V.2).mulVec uv.2)} ⊆
      {V | ¬ Function.Injective (joinedFree (freePart V.1,freePart V.2)).mulVec} := by
    intro V hV hZ
    exact hV (AffineSliceIndependence.point_pair_independent s V.1 V.2 hZ)
  have hh := p.toOuterMeasure.mono hsub
  change p.toOuterMeasure {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
      (pointColumns (degree := degree) s V.1).mulVec uv.1+
        (pointColumns (degree := degree) s V.2).mulVec uv.2)} ≤
    p.toOuterMeasure {V | ¬ Function.Injective (joinedFree (freePart V.1,freePart V.2)).mulVec} at hh
  rw [he] at hh
  exact hh.trans (by simpa only [Fintype.card_option,Fintype.card_sum,Fintype.card_fin,two_mul,add_assoc,add_comm,add_left_comm]
    using (GramNormalization.column_failure (J := Option (D ⊕ D)) (N := Fin n)))

/--
---
conclusion: Lax342547.ConditionedAffineColumns.conditioning_pair_bound
---
-/
theorem conditioning_pair_bound {A : Type} [Fintype A] (ρ : A → ℝ) (C : A → Prop)
    (bad : A × A → Prop) (β δ : ℝ) (hρ : ∀ a,0 ≤ ρ a) (hβ : 0 < β)
    (hC : β ≤ cellMass ρ C)
    (hbad : cellMass (fun z : A × A => ρ z.1*ρ z.2) bad ≤ δ) :
    cellMass (fun z : A × A => conditionalLaw ρ C z.1*conditionalLaw ρ C z.2) bad ≤ δ/β^2 := by
  classical
  have hc (a : A) : conditionalLaw ρ C a ≤ ρ a/β := by
    unfold conditionalLaw
    split_ifs
    · exact div_le_div_of_nonneg_left (hρ a) hβ hC
    · simpa only [zero_div] using div_nonneg (hρ a) hβ.le
  have hn a : 0 ≤ conditionalLaw ρ C a := RetainedImages.conditional_law_nonneg ρ C hρ a
  calc
    _ ≤ cellMass (fun z : A × A => ρ z.1*ρ z.2) bad/β^2 := by
      unfold cellMass
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : bad z
      · simp only [if_pos hz]
        have hh := mul_le_mul (hc z.1) (hc z.2) (hn z.2) (div_nonneg (hρ z.1) hβ.le)
        simpa only [div_mul_div_comm,pow_two] using hh
      · simp [hz]
    _ ≤ δ/β^2 := div_le_div_of_nonneg_right hbad (sq_nonneg β)

theorem uniform_pair_weights {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (z : A × B) : weights (PMF.uniformOfFintype (A × B)) z =
      weights (PMF.uniformOfFintype A) z.1*weights (PMF.uniformOfFintype B) z.2 := by
  simp only [weights,PMF.uniformOfFintype_apply,Fintype.card_prod,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Nat.cast_mul,ENNReal.toReal_mul,mul_inv_rev]
  ring

/--
---
conclusion: Lax342547.ConditionedAffineColumns.conditioned_nominal_pair_failure
---
-/
theorem conditioned_nominal_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) (C : Matrix (Base k n) (Option D) Binary → Prop) (β : ℝ)
    (hβ : 0 < β) (hC : β ≤ cellMass
      (weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary))) C) :
    cellMass (fun V : Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary =>
        conditionalLaw (weights (PMF.uniformOfFintype _)) C V.1*
          conditionalLaw (weights (PMF.uniformOfFintype _)) C V.2)
      (fun V => ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s V.1).mulVec uv.1+
          (pointColumns (degree := degree) s V.2).mulVec uv.2)) ≤
      ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2 := by
  classical
  have hf := ENNReal.toReal_mono (by apply ENNReal.div_ne_top <;> simp :
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n ≠ ⊤)
      (nominal_pair_failure (k := k) (n := n) (degree := degree) (D := D) s)
  rw [← RealCellLaws.event_mass] at hf
  simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat] at hf
  have he : weights (PMF.uniformOfFintype
      (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)) =
      (fun V => weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary)) V.1*
        weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary)) V.2) :=
    funext uniform_pair_weights
  rw [he] at hf
  exact conditioning_pair_bound _ C _ β _ (RealCellLaws.weights_nonneg _) hβ hC hf

end
end Lax342547Proofs.ConditionedAffineColumns
