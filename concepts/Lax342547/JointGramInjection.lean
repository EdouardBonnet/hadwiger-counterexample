import Lax342547.GramOrbitDensity

/-!
---
title: Joint-injectivity loss for two actual reference batches
type: definition and theorem
---
Concatenating both column lists turns the ambient reference experiment into
a uniform matrix pair. The separate Gram-orbit caps transfer column failure
to the actual product law; Fourier normalization also bounds that loss after
conditioning on reciprocal Gram entries.
-/

namespace Lax342547.JointGramInjection
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.GramOrbitDensity Lax342547.RetainedImages
open scoped BigOperators ENNReal

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

def ambientEquiv :
    ((N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) ≃
      (Matrix N (I ⊕ K) Binary × Matrix N (J ⊕ L) Binary) where
  toFun z := (Matrix.fromCols (batchEquiv.symm z.1).1 (batchEquiv.symm z.2).1,
    Matrix.fromCols (batchEquiv.symm z.1).2 (batchEquiv.symm z.2).2)
  invFun z := (batchEquiv (z.1.submatrix id Sum.inl,z.2.submatrix id Sum.inl),
    batchEquiv (z.1.submatrix id Sum.inr,z.2.submatrix id Sum.inr))
  left_inv z := by apply Prod.ext <;> funext (n,s) <;> cases s <;> rfl
  right_inv z := by apply Prod.ext <;> ext n (i | k) <;> rfl

def Good (z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary)) :=
  Function.Injective (ambientEquiv z).1.mulVec ∧ Function.Injective (ambientEquiv z).2.mulVec

axiom ambient_failure [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N] :
    (PMF.uniformOfFintype ((N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary))).toOuterMeasure
        {z | ¬ Good z} ≤
      ((2 : ℝ≥0∞)^(Fintype.card I+Fintype.card K)+(2 : ℝ≥0∞)^(Fintype.card J+Fintype.card L))/
        (2 : ℝ≥0∞)^Fintype.card N

axiom reference_failure [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N] (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ Fintype.card N)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ Fintype.card N) :
    cellMass (fun z : (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary) =>
        batchLaw (N := N) G z.1*batchLaw (N := N) H z.2) (fun z => ¬ Good z) ≤
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
        (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/
          (2 : ℝ)^Fintype.card N)

axiom conditioned_reference_failure {I J K L : Type} [Fintype I] [Fintype J]
    [Fintype K] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    (target : Lax342547.CrossGramBasis.Slots I J K L → Binary)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    cellMass (fun z : (Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary) =>
        batchLaw G z.1*batchLaw H z.2)
      (fun z => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n z = target ∧ ¬ Good z)/
      Lax342547.FourierTests.patternMass (fun z => batchLaw G z.1*batchLaw H z.2)
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n) target ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)*
        (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
          (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n))

end
end Lax342547.JointGramInjection
