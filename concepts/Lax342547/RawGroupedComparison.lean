import Lax342547.GroupTensorComparison

/-!
---
title: Actual grouped raw observations with arbitrary common tests
type: lemma
---
Nominal joint independence is checked separately in every component and
sign. Independent raw frame groups then compare arbitrary common tests of
the separate observed arrays, with the sum of their explicit two-batch
errors. Both Gram matrices and column dimensions may vary by group.
-/

namespace Lax342547.RawGroupedComparison
noncomputable section
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.GramOrbitDensity
open Lax342547.FrameTuples Lax342547.RealCellLaws Lax342547.RawFrameComparison
open scoped BigOperators

variable {S B H : Type} [Fintype S] [DecidableEq S] [Fintype B] [Fintype H]
  {I J K L : S → Type} [∀ s,Fintype (I s)] [∀ s,Fintype (J s)]
  [∀ s,Fintype (K s)] [∀ s,Fintype (L s)]

axiom primal_groups [∀ s,DecidableEq (I s)] [∀ s,DecidableEq (J s)]
    [∀ s,DecidableEq (K s)] [∀ s,DecidableEq (L s)] (n : ℕ) (E : S → Matrix B B Binary)
    [∀ s,Nonempty (Frame B H (Fin n) (E s))]
    (C₁ : ∀ s,Matrix B (I s) Binary) (D₁ : ∀ s,Matrix B (J s) Binary)
    (C₂ : ∀ s,Matrix B (K s) Binary) (D₂ : ∀ s,Matrix B (L s) Binary)
    (hC : ∀ s,Function.Injective (Matrix.fromCols (C₁ s) (C₂ s)).mulVec)
    (hD : ∀ s,Function.Injective (Matrix.fromCols (D₁ s) (D₂ s)).mulVec)
    (f : (∀ s,Fin n × (I s ⊕ J s) → Binary) → ℝ)
    (g : (∀ s,Fin n × (K s ⊕ L s) → Binary) → ℝ)
    (hN₁ : ∀ s,Fintype.card (I s)+Fintype.card (J s)+1 ≤ n)
    (hN₂ : ∀ s,Fintype.card (K s)+Fintype.card (L s)+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ∀ s,((2 : ℝ)^(Fintype.card (I s)*Fintype.card (J s)+2))*
        ((2 : ℝ)^(Fintype.card (K s)*Fintype.card (L s)+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (I s) (J s) (K s) (L s))+1)) :
    |(∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        (f (fun s => batchEquiv ((o s).P*C₁ s,(o s).Q*D₁ s))*
          g (fun s => batchEquiv ((o s).P*C₂ s,(o s).Q*D₂ s))))-
      (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        f (fun s => batchEquiv ((o s).P*C₁ s,(o s).Q*D₁ s)))*
      (∑ o : ∀ s,Frame B H (Fin n) (E s),weights (PMF.uniformOfFintype _) o*
        g (fun s => batchEquiv ((o s).P*C₂ s,(o s).Q*D₂ s)))| ≤
      ∑ s,errorBound n (I s) (J s) (K s) (L s)

axiom full_groups [∀ s,DecidableEq (I s)] [∀ s,DecidableEq (J s)]
    [∀ s,DecidableEq (K s)] [∀ s,DecidableEq (L s)] (n : ℕ) (E : S → Matrix B B Binary) (T : S → Matrix H H Binary)
    [∀ s,Nonempty (ChannelFiber (N := Fin n) (E s) (T s))]
    (C₁ : ∀ s,Matrix (B ⊕ H) (I s) Binary) (D₁ : ∀ s,Matrix (B ⊕ H) (J s) Binary)
    (C₂ : ∀ s,Matrix (B ⊕ H) (K s) Binary) (D₂ : ∀ s,Matrix (B ⊕ H) (L s) Binary)
    (hC : ∀ s,Function.Injective (Matrix.fromCols (C₁ s) (C₂ s)).mulVec)
    (hD : ∀ s,Function.Injective (Matrix.fromCols (D₁ s) (D₂ s)).mulVec)
    (f : (∀ s,Fin n × (I s ⊕ J s) → Binary) → ℝ)
    (g : (∀ s,Fin n × (K s ⊕ L s) → Binary) → ℝ)
    (hN₁ : ∀ s,Fintype.card (I s)+Fintype.card (J s)+1 ≤ n)
    (hN₂ : ∀ s,Fintype.card (K s)+Fintype.card (L s)+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ∀ s,((2 : ℝ)^(Fintype.card (I s)*Fintype.card (J s)+2))*
        ((2 : ℝ)^(Fintype.card (K s)*Fintype.card (L s)+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (I s) (J s) (K s) (L s))+1)) :
    |(∑ o : ∀ s,ChannelFiber (N := Fin n) (E s) (T s),weights (PMF.uniformOfFintype _) o*
        (f (fun s => batchEquiv ((Lax342547.FrameSymmetry.plus (o s).val).val*C₁ s,(Lax342547.FrameSymmetry.minus (o s).val).val*D₁ s))*
          g (fun s => batchEquiv ((Lax342547.FrameSymmetry.plus (o s).val).val*C₂ s,(Lax342547.FrameSymmetry.minus (o s).val).val*D₂ s))))-
      (∑ o : ∀ s,ChannelFiber (N := Fin n) (E s) (T s),weights (PMF.uniformOfFintype _) o*
        f (fun s => batchEquiv ((Lax342547.FrameSymmetry.plus (o s).val).val*C₁ s,(Lax342547.FrameSymmetry.minus (o s).val).val*D₁ s)))*
      (∑ o : ∀ s,ChannelFiber (N := Fin n) (E s) (T s),weights (PMF.uniformOfFintype _) o*
        g (fun s => batchEquiv ((Lax342547.FrameSymmetry.plus (o s).val).val*C₂ s,(Lax342547.FrameSymmetry.minus (o s).val).val*D₂ s)))| ≤
      ∑ s,errorBound n (I s) (J s) (K s) (L s)

end
end Lax342547.RawGroupedComparison
