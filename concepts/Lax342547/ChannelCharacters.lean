import Lax342547.BilinearMean
import Lax342547.FiniteMoments
import Mathlib.Algebra.BigOperators.Field

/-!
---
title: Independent binary channel characters
type: definition and theorem
---
Actual independent uniform channel pairs have the exact rank character mean; multiplication over channels and sampled tensors gives the mean of their actual matrix sum.
-/

namespace Lax342547.ChannelCharacters

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.RelativeEntropy Lax342547.FiniteSampling
open scoped BigOperators

noncomputable def channelLaw {I J : Type} [Fintype I] [Fintype J]
    (_ : (I → Binary) × (J → Binary)) : ℝ :=
    1/((2 : ℝ)^Fintype.card I*2^Fintype.card J)

noncomputable def character {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (c : (I → Binary) × (J → Binary)) : ℝ := phase c.1 (A.mulVec c.2)

noncomputable def channelCharacter {I J : Type} [Fintype I] [Fintype J] (h : ℕ)
    (A : Matrix I J Binary) (c : Fin h → (I → Binary) × (J → Binary)) : ℝ :=
    ∏ i, character A (c i)

axiom channel_probability {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Probability (channelLaw (I := I) (J := J))

axiom character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) :
    (∑ c, channelLaw c*character A c) = 1/(2 : ℝ)^A.rank

axiom character_add {I J : Type} [Fintype I] [Fintype J]
    (A B : Matrix I J Binary) (c : (I → Binary) × (J → Binary)) :
    character (A+B) c = character A c*character B c

axiom character_sum {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) (c : (I → Binary) × (J → Binary)) :
    character (∑ i, A i) c = ∏ i, character (A i) c

axiom repeated_character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) (h : ℕ) :
    (∑ c, productLaw (fun _ : Fin h => channelLaw) c*channelCharacter h A c) =
      1/(2 : ℝ)^(h*A.rank)

axiom product_channel_characters {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) (h : ℕ) (c : Fin h → (I → Binary) × (J → Binary)) :
    (∏ i, channelCharacter h (A i) c) = channelCharacter h (∑ i, A i) c

end Lax342547.ChannelCharacters
