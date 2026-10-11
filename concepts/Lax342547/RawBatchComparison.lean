import Lax342547.JoinedGramOrbits
import Lax342547.JointGramInjection

/-!
---
title: Bounded tests under the actual two-batch Gram law
type: lemma
---
The union orbit is exactly the product of its separate orbit laws conditioned
on reciprocal Gram entries and joint column injectivity. Removing only the
joint-injectivity event costs its actual conditional mass; the remaining
comparison uses the separately capped batch laws and independent Gram characters.
-/

namespace Lax342547.RawBatchComparison
noncomputable section
open Lax342547.MomentSpace Lax342547.FrameTuples Lax342547.RealCellLaws
open Lax342547.GramOrbitDensity Lax342547.RetainedImages
open scoped BigOperators

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] [DecidableEq N]

def flat (G : Matrix I J Binary) (H : Matrix K L Binary)
    (z : Orbit N G × Orbit N H) :
    (N × (I ⊕ J) → Binary) × (N × (K ⊕ L) → Binary) :=
  (batchEquiv z.1.val,batchEquiv z.2.val)
def target (A : Matrix I L Binary) (B : Matrix K J Binary) :
    Lax342547.CrossGramBasis.Slots I J K L → Binary
  | Sum.inl (i,l) => A i l
  | Sum.inr (j,k) => B k j

axiom union_conditional_integral (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (test : ((Fin n × (I ⊕ J) → Binary) × (Fin n × (K ⊕ L) → Binary)) → ℝ) :
    (∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),
      weights (PMF.uniformOfFintype _) z*test (Lax342547.JointGramInjection.ambientEquiv.symm z.val)) =
    ∑ x,conditionalLaw (fun x => batchLaw G x.1*batchLaw H x.2)
      (fun x => Lax342547.CrossBatchMixing.crossBits Lax342547.CrossGramBasis.tests n x = target A B ∧
        Lax342547.JointGramInjection.Good x) x*test x

axiom union_test_comparison (n : ℕ) (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit (Fin n) G)] [Nonempty (Orbit (Fin n) H)]
    [Nonempty (Orbit (Fin n) (Matrix.fromBlocks G A B H))]
    (f : (Fin n × (I ⊕ J) → Binary) → ℝ) (g : (Fin n × (K ⊕ L) → Binary) → ℝ)
    (hN₁ : Fintype.card I+Fintype.card J+1 ≤ n)
    (hN₂ : Fintype.card K+Fintype.card L+1 ≤ n)
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hsmall : ((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
        ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+1)) :
    |(∑ z : Orbit (Fin n) (Matrix.fromBlocks G A B H),weights (PMF.uniformOfFintype _) z*
        (f (Lax342547.JointGramInjection.ambientEquiv.symm z.val).1*
          g (Lax342547.JointGramInjection.ambientEquiv.symm z.val).2))-
      (∑ x,batchLaw G x*f x)*(∑ y,batchLaw H y*g y)| ≤
      (2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots I J K L)+2)*
        ((((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
          ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))/Real.sqrt ((2 : ℝ)^n))+
          (((2 : ℝ)^(Fintype.card I*Fintype.card J+2))*
            ((2 : ℝ)^(Fintype.card K*Fintype.card L+2))*
            (((2 : ℝ)^(Fintype.card I+Fintype.card K)+(2 : ℝ)^(Fintype.card J+Fintype.card L))/(2 : ℝ)^n)))

end
end Lax342547.RawBatchComparison
