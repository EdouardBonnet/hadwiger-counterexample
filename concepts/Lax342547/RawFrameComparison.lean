import Lax342547.RawBatchComparison

/-!
---
title: Actual raw frame observations with uniform two-batch decay
type: lemma
---
Independent combined coefficient columns give a comparison for arbitrary
separate bounded tests under the actual raw frame law, or under the full
self-channel Gram fiber law. The explicit threshold and error constants
depend only on the four fixed column counts and not on their Gram entries.
-/

namespace Lax342547.RawFrameComparison
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.GramOrbitDensity Lax342547.RawFrames
open scoped BigOperators

def errorBound (n : ℕ) (I J K L : Type) [Fintype I] [Fintype J] [Fintype K] [Fintype L] : ℝ :=
  (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
    ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
      ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
      (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
        (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)))

def scale (I J K L : Type) [Fintype I] [Fintype J] [Fintype K] [Fintype L] : ℝ :=
  (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
    ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
    ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
    (1+((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L)))

axiom errorBound_half_decay (n : ℕ) (I J K L : Type)
    [Fintype I] [Fintype J] [Fintype K] [Fintype L] :
    errorBound n I J K L ≤ scale I J K L/Real.sqrt ((2 : ℝ)^n)

axiom eventually_valid (I J K L : Type) [Fintype I] [Fintype J] [Fintype K] [Fintype L] :
    ∃ n₀ : ℕ,∀ n ≥ n₀,Fintype.card I+Fintype.card J+1 ≤ n ∧
      Fintype.card K+Fintype.card L+1 ≤ n ∧
      ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
        1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable {B H : Type} [Fintype B] [Fintype H]

axiom primal_test_comparison [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] (n : ℕ) (E : Matrix B B Binary)
    [Nonempty (Frame B H (Fin n) E)]
    (C₁ : Matrix B I Binary) (D₁ : Matrix B J Binary)
    (C₂ : Matrix B K Binary) (D₂ : Matrix B L Binary)
    (hC : Function.Injective (Matrix.fromCols C₁ C₂).mulVec)
    (hD : Function.Injective (Matrix.fromCols D₁ D₂).mulVec)
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*
        (f (batchEquiv (F.P*C₁,F.Q*D₁))*g (batchEquiv (F.P*C₂,F.Q*D₂))))-
      (∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*f (batchEquiv (F.P*C₁,F.Q*D₁)))*
      (∑ F : Frame B H (Fin n) E,weights (PMF.uniformOfFintype _) F*g (batchEquiv (F.P*C₂,F.Q*D₂)))| ≤
        errorBound n I J K L

axiom full_test_comparison [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] (n : ℕ) (E : Matrix B B Binary) (S : Matrix H H Binary)
    [Nonempty (ChannelFiber (N := Fin n) E S)]
    (C₁ : Matrix (B ⊕ H) I Binary) (D₁ : Matrix (B ⊕ H) J Binary)
    (C₂ : Matrix (B ⊕ H) K Binary) (D₂ : Matrix (B ⊕ H) L Binary)
    (hC : Function.Injective (Matrix.fromCols C₁ C₂).mulVec)
    (hD : Function.Injective (Matrix.fromCols D₁ D₂).mulVec)
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*
        (f (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁))*g (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂))))-
      (∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*f (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₁,(Lax342547.FrameSymmetry.minus F.val).val*D₁)))*
      (∑ F : ChannelFiber (N := Fin n) E S,weights (PMF.uniformOfFintype _) F*g (batchEquiv ((Lax342547.FrameSymmetry.plus F.val).val*C₂,(Lax342547.FrameSymmetry.minus F.val).val*D₂)))| ≤
        errorBound n I J K L

end
end Lax342547.RawFrameComparison
