import Lax342547.ChannelMoments

/-!
---
title: Characters of all independent tensor channels
type: definition and theorem
---
Multiplication over actual component channel pairs yields the exact exponent given by the sum of component ranks, including the actual sampled componentwise tensor sum.
-/

namespace Lax342547.TensorCharacters

open Lax342547.MomentSpace Lax342547.ChannelCharacters Lax342547.FiniteSampling
open scoped BigOperators

noncomputable def tensorCharacter {e I J : Type} [Fintype e] [Fintype I] [Fintype J] (h : ℕ)
    (A : e → Matrix I J Binary) (c : e × Fin h → (I → Binary) × (J → Binary)) : ℝ :=
    ∏ i, character (A i.1) (c i)

axiom tensor_character_average {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (A : e → Matrix I J Binary) (h : ℕ) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*tensorCharacter h A c) =
      1/(2 : ℝ)^(h*∑ i, (A i).rank)

axiom product_tensor_characters {e I J ι : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → e → Matrix I J Binary) (h : ℕ) (c : e × Fin h → (I → Binary) × (J → Binary)) :
    (∏ i, tensorCharacter h (A i) c) = tensorCharacter h (fun e => ∑ i, A i e) c

end Lax342547.TensorCharacters
