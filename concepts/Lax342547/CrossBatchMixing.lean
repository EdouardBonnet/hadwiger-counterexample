import Lax342547.ConditionedMixing
import Lax342547.SlotWalsh
import Lax342547.RelativeEntropy

/-!
---
title: Quantitative comparison after cross-batch Gram conditioning
type: lemma
---
The actual cross-slot coefficient matrices give bit rank at least N for
every nontrivial character. Separate bounded-density batch laws and bounded
tests retain a uniform comparison after mutual Gram conditioning.
-/

namespace Lax342547.CrossBatchMixing

open Lax342547.MomentSpace Lax342547.SlotWalsh Lax342547.FourierTests Lax342547.RelativeEntropy

noncomputable def coefficient {I J S : Type} [Fintype S]
    (C : S → Matrix I J Binary) (t : S → Binary) : Matrix I J Binary := ∑ s,t s • C s

def crossBits {I J S : Type} [Fintype I] [Fintype J] (C : S → Matrix I J Binary) (N : ℕ)
    (xy : ((Fin N × I → Binary) × (Fin N × J → Binary))) : S → Binary :=
  fun s => dotProduct xy.1 ((bitMatrix (C s) N).mulVec xy.2)

axiom weighted_character_bound {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    [DecidableEq I] [DecidableEq J] (C : S → Matrix I J Binary) (N : ℕ)
    (α f : (Fin N × I → Binary) → ℝ) (β g : (Fin N × J → Binary) → ℝ)
    (target t : S → Binary) (C₁ C₂ : ℝ)
    (hα : ∀ x,0 ≤ α x ∧ α x ≤ C₁/(2 : ℝ)^(N*Fintype.card I))
    (hβ : ∀ y,0 ≤ β y ∧ β y ≤ C₂/(2 : ℝ)^(N*Fintype.card J))
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hC : coefficient C t ≠ 0) :
    |characterMean (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
      α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target t| ≤
      C₁*C₂/Real.sqrt ((2 : ℝ)^N)

axiom cross_batch_comparison {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    [DecidableEq I] [DecidableEq J] [DecidableEq S] (C : S → Matrix I J Binary) (N : ℕ)
    (α f : (Fin N × I → Binary) → ℝ) (β g : (Fin N × J → Binary) → ℝ)
    (target : S → Binary) (C₁ C₂ : ℝ)
    (hα : Probability α) (hβ : Probability β)
    (hcapA : ∀ x,α x ≤ C₁/(2 : ℝ)^(N*Fintype.card I))
    (hcapB : ∀ y,β y ≤ C₂/(2 : ℝ)^(N*Fintype.card J))
    (hf : ∀ x,|f x| ≤ 1) (hg : ∀ y,|g y| ≤ 1)
    (hC : ∀ t : S → Binary,t ≠ 0 → coefficient C t ≠ 0)
    (hsmall : C₁*C₂/Real.sqrt ((2 : ℝ)^N) ≤ 1/(2 : ℝ)^(Fintype.card S+1)) :
    |patternMass (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
        α xy.1*β xy.2*(f xy.1*g xy.2)) (crossBits C N) target/
        patternMass (fun xy : (Fin N × I → Binary) × (Fin N × J → Binary) =>
          α xy.1*β xy.2) (crossBits C N) target-
        (∑ x,α x*f x)*(∑ y,β y*g y)| ≤
      (2 : ℝ)^(Fintype.card S+2)*(C₁*C₂/Real.sqrt ((2 : ℝ)^N))

end Lax342547.CrossBatchMixing
