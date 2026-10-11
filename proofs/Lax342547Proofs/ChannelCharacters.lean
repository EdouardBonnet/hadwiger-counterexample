import Lax342547.ChannelCharacters
import Mathlib.Algebra.BigOperators.Field
import Lax342547.BilinearMean
import Lax342547Proofs.Walsh

namespace Lax342547Proofs.ChannelCharacters
open Lax342547.ChannelCharacters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.RelativeEntropy Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.ChannelCharacters.channel_probability
---
-/
theorem channel_probability {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] :
    Probability (channelLaw (I := I) (J := J)) := by
  classical
  constructor
  · intro x; unfold channelLaw; positivity
  · simp only [channelLaw,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simp only [Fintype.card_prod,Fintype.card_fun,Binary,ZMod.card,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    field_simp

/--
---
conclusion: Lax342547.ChannelCharacters.character_average
---
-/
theorem character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) :
    (∑ c, channelLaw c*character A c) = 1/(2 : ℝ)^A.rank := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [channelLaw,character,div_mul_eq_mul_div,one_mul]
  calc
    _ = (∑ x : I → Binary, ∑ y : J → Binary, phase x (A.mulVec y))/
        ((2 : ℝ)^Fintype.card I*2^Fintype.card J) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_div]
    _ = _ := Lax342547.BilinearMean.bilinear_character_average A

/--
---
conclusion: Lax342547.ChannelCharacters.character_add
---
-/
theorem character_add {I J : Type} [Fintype I] [Fintype J]
    (A B : Matrix I J Binary) (c : (I → Binary) × (J → Binary)) :
    character (A+B) c = character A c*character B c := by
  unfold character phase
  rw [Matrix.add_mulVec,dotProduct_add,Lax342547Proofs.Walsh.sign_add]

/--
---
conclusion: Lax342547.ChannelCharacters.character_sum
---
-/
theorem character_sum {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) (c : (I → Binary) × (J → Binary)) :
    character (∑ i, A i) c = ∏ i, character (A i) c := by
  classical
  have hh (T : Finset ι) : character (∑ i ∈ T, A i) c = ∏ i ∈ T, character (A i) c := by
    induction T using Finset.induction_on with
    | empty => simp [character,phase,Lax342547Proofs.Walsh.sign_zero]
    | @insert i T hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,Lax342547.ChannelCharacters.character_add,ih]
  exact hh Finset.univ

/--
---
conclusion: Lax342547.ChannelCharacters.repeated_character_average
---
-/
theorem repeated_character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) (h : ℕ) :
    (∑ c, productLaw (fun _ : Fin h => channelLaw) c*channelCharacter h A c) =
      1/(2 : ℝ)^(h*A.rank) := by
  classical
  simp only [productLaw,channelCharacter,← Finset.prod_mul_distrib]
  calc
    _ = ∏ _i : Fin h, ∑ c : (I → Binary) × (J → Binary), channelLaw c*character A c :=
      (Fintype.prod_sum (fun _i : Fin h => fun c : (I → Binary) × (J → Binary) => channelLaw c*character A c)).symm
    _ = _ := by
      simp_rw [Lax342547.ChannelCharacters.character_average]
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_div_pow,← pow_mul,Nat.mul_comm]

/--
---
conclusion: Lax342547.ChannelCharacters.product_channel_characters
---
-/
theorem product_channel_characters {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) (h : ℕ) (c : Fin h → (I → Binary) × (J → Binary)) :
    (∏ i, channelCharacter h (A i) c) = channelCharacter h (∑ i, A i) c := by
  classical
  unfold channelCharacter
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact (Lax342547.ChannelCharacters.character_sum A (c j)).symm

end Lax342547Proofs.ChannelCharacters
