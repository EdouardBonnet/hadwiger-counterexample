import Lax342547.AffineSliceIndependence
import Lax342547.RealCellLaws

/-!
---
title: Actual conditioned affine coefficient dependence bounds
type: lemma
---
The free parts of two independent full affine coefficient maps remain a
uniform matrix pair. This pays nominal dependence before conditioning;
conditioning each coefficient draw on an event of mass at least beta
increases that failure bound by at most beta to the power minus two.
-/

namespace Lax342547.ConditionedAffineColumns
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.AffineSliceIndependence Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal

def freePairMap {k n : ℕ} {D : Type} :
    (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary) →ₗ[Binary]
      (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary) where
  toFun V := (freePart V.1,freePart V.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

axiom freePair_uniform {k n : ℕ} {D : Type} [Fintype D] [DecidableEq D] :
    (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)).map
      (freePairMap (k := k) (n := n) (D := D)) =
      PMF.uniformOfFintype (Matrix (Fin n) (Option D) Binary × Matrix (Fin n) (Option D) Binary)

axiom nominal_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) :
    (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary)).toOuterMeasure
      {V | ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s V.1).mulVec uv.1+
          (pointColumns (degree := degree) s V.2).mulVec uv.2)} ≤
      (2 : ℝ≥0∞)^(2*Fintype.card D+1)/(2 : ℝ≥0∞)^n

axiom conditioning_pair_bound {A : Type} [Fintype A] (ρ : A → ℝ) (C : A → Prop)
    (bad : A × A → Prop) (β δ : ℝ) (hρ : ∀ a,0 ≤ ρ a) (hβ : 0 < β)
    (hC : β ≤ cellMass ρ C)
    (hbad : cellMass (fun z : A × A => ρ z.1*ρ z.2) bad ≤ δ) :
    cellMass (fun z : A × A => conditionalLaw ρ C z.1*conditionalLaw ρ C z.2) bad ≤ δ/β^2

axiom conditioned_nominal_pair_failure {k n b degree : ℕ} {D : Type} [Fintype D] [DecidableEq D]
    (s : Fin b → Binary) (C : Matrix (Base k n) (Option D) Binary → Prop) (β : ℝ)
    (hβ : 0 < β) (hC : β ≤ cellMass
      (weights (PMF.uniformOfFintype (Matrix (Base k n) (Option D) Binary))) C) :
    cellMass (fun V : Matrix (Base k n) (Option D) Binary × Matrix (Base k n) (Option D) Binary =>
        conditionalLaw (weights (PMF.uniformOfFintype _)) C V.1*
          conditionalLaw (weights (PMF.uniformOfFintype _)) C V.2)
      (fun V => ¬ Function.Injective (fun uv : (Option D → Binary) × (Option D → Binary) =>
        (pointColumns (degree := degree) s V.1).mulVec uv.1+
          (pointColumns (degree := degree) s V.2).mulVec uv.2)) ≤
      ((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2

end
end Lax342547.ConditionedAffineColumns
