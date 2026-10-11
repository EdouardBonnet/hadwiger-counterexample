import Lax342547.FrameTuples
import Lax342547.RealCellLaws
import Lax342547.CrossGramBasis

/-!
---
title: Actual reference-batch laws for mutual Gram tests
type: lemma
---
Flatten both signs of a paired Gram orbit into one batch. Its independent-bit
density denominator is explicit; arbitrary tests retain the reciprocal
mutual-Gram comparison with no independence assumption inside either batch.
-/

namespace Lax342547.GramOrbitDensity

open Lax342547.RelativeEntropy
open scoped BigOperators

open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws

def batchEquiv {I J N : Type} :
    (Matrix N I Binary × Matrix N J Binary) ≃ (N × (I ⊕ J) → Binary) where
  toFun z p := match p.2 with
    | Sum.inl i => z.1 p.1 i
    | Sum.inr j => z.2 p.1 j
  invFun x := (fun n i => x (n,Sum.inl i),fun n j => x (n,Sum.inr j))
  left_inv z := rfl
  right_inv x := by funext p; rcases p with ⟨n,i|j⟩ <;> rfl

noncomputable def batchLaw {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq N] (G : Matrix I J Binary) [Nonempty (Orbit N G)] :
    (N × (I ⊕ J) → Binary) → ℝ :=
  weights ((PMF.uniformOfFintype (Orbit N G)).map (fun z => batchEquiv z.val))

axiom batch_probability {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    [Nonempty (Orbit N G)] : Probability (batchLaw (N := N) G)

axiom batch_point_cap {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    [Nonempty (Orbit N G)] (hN : Fintype.card I+Fintype.card J+1 ≤ Fintype.card N)
    (x : N × (I ⊕ J) → Binary) :
    batchLaw G x ≤ (2 : ℝ)^(Fintype.card I*Fintype.card J+2)/
      (2 : ℝ)^(Fintype.card N*(Fintype.card I+Fintype.card J))

axiom mutual_gram_comparison {I J K L : Type} [Fintype I] [Fintype J]
    [Fintype K] [Fintype L] [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]
    (N : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    [Nonempty (Orbit (Fin N) G)] [Nonempty (Orbit (Fin N) H)]
    (f : (Fin N × (I ⊕ J) → Binary) → ℝ) (g : (Fin N × (K ⊕ L) → Binary) → ℝ)
    (target : Lax342547.CrossGramBasis.Slots I J K L → Binary)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ N)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ N)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |Lax342547.FourierTests.patternMass (fun xy => batchLaw G xy.1*batchLaw H xy.2*(f xy.1*g xy.2))
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests N) target /
      Lax342547.FourierTests.patternMass (fun xy => batchLaw G xy.1*batchLaw H xy.2)
        (Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests N) target -
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^N))

end Lax342547.GramOrbitDensity
