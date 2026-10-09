import Lax342547.GramColumns

/-!
---
title: Two-sided Gram normalization for individually injective frames
type: definition and theorem
---
Lemma 4.2, stated with exact finite probabilities and ratios of powers of
two. Subtraction in the extended nonnegative reals is truncated at zero;
when p+q≤N this is the displayed lower bound in the paper.
-/

namespace Lax342547.GramNormalization

open Lax342547.MomentSpace
open scoped ENNReal

noncomputable def probability {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Matrix N I Binary × Matrix N J Binary)).toOuterMeasure
    {z | Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec ∧ z.1.transpose * z.2 = G}

axiom column_failure {J N : Type} [Fintype J] [Fintype N] [DecidableEq J] [DecidableEq N] :
    (PMF.uniformOfFintype (Matrix N J Binary)).toOuterMeasure {A | ¬ Function.Injective A.mulVec} ≤
      (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Fintype.card N

axiom normalization_upper {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) :
    probability (N := N) G ≤ 1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)

axiom normalization_lower {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) :
    (1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J)) *
      (1 - (2 : ℝ≥0∞) ^ Fintype.card I / 2 ^ Fintype.card N) *
      (1 - (2 : ℝ≥0∞) ^ (Fintype.card I + Fintype.card J) / 2 ^ Fintype.card N) ≤
        probability (N := N) G

axiom normalization_quarter {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I + Fintype.card J + 1 ≤ Fintype.card N) :
    1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card J + 2) ≤ probability (N := N) G

end Lax342547.GramNormalization
