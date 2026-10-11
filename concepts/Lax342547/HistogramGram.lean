import Lax342547.GramNormalization

/-!
---
title: Uniform relative Gram normalization errors
type: lemma
---
The actual injective Gram event differs from its independent-bit factor
by at most twice the column-rank exception. Independent groups multiply
with an additive relative error budget, including growing slot batches.
-/

namespace Lax342547.HistogramGram

open Lax342547.MomentSpace
open scoped BigOperators

noncomputable def normalized {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary) : ℝ :=
  (2 : ℝ)^(Fintype.card I*Fintype.card J)*(Lax342547.GramNormalization.probability (N := N) G).toReal

axiom normalized_bounds {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N) :
    0 ≤ normalized (N := N) G ∧ normalized (N := N) G ≤ 1 ∧
      1-2*((2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N) ≤ normalized (N := N) G

axiom normalized_error {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N) :
    |normalized (N := N) G-1| ≤
      2*((2 : ℝ)^(Fintype.card I+Fintype.card J)/(2 : ℝ)^Fintype.card N)

axiom product_error {D : Type} (S : Finset D) (q ε : D → ℝ)
    (hq : ∀ d ∈ S,0 ≤ q d ∧ q d ≤ 1) (hε : ∀ d ∈ S,0 ≤ ε d)
    (herr : ∀ d ∈ S,1-ε d ≤ q d) :
    |(∏ d ∈ S,q d)-1| ≤ ∑ d ∈ S,ε d

axiom independent_groups_error {S N : Type} [Fintype S] [Fintype N] [DecidableEq N]
    {I J : S → Type} [∀ s,Fintype (I s)] [∀ s,Fintype (J s)]
    [∀ s,DecidableEq (I s)] [∀ s,DecidableEq (J s)]
    (G : ∀ s,Matrix (I s) (J s) Binary)
    (hN : ∀ s,Fintype.card (I s)+Fintype.card (J s) ≤ Fintype.card N) :
    |(∏ s,normalized (N := N) (G s))-1| ≤
      ∑ s,2*((2 : ℝ)^(Fintype.card (I s)+Fintype.card (J s))/(2 : ℝ)^Fintype.card N)

axiom half_ambient_error {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq I] [DecidableEq J] [DecidableEq N] (G : Matrix I J Binary)
    (hN : Fintype.card I+Fintype.card J ≤ Fintype.card N/2) :
    |normalized (N := N) G-1| ≤ 2/(2 : ℝ)^(Fintype.card N/2)

end Lax342547.HistogramGram
