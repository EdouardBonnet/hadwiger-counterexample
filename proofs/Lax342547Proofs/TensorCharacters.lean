import Lax342547.TensorCharacters
import Lax342547Proofs.ChannelMoments

namespace Lax342547Proofs.TensorCharacters
open Lax342547.TensorCharacters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ChannelCharacters Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.TensorCharacters.tensor_character_average
---
-/
theorem tensor_character_average {e I J : Type} [Fintype e] [Fintype I] [Fintype J]
    [DecidableEq e] [DecidableEq I] [DecidableEq J] (A : e → Matrix I J Binary) (h : ℕ) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*tensorCharacter h A c) =
      1/(2 : ℝ)^(h*∑ i, (A i).rank) := by
  classical
  simp only [productLaw,tensorCharacter,← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : e × Fin h, ∑ c : (I → Binary) × (J → Binary), channelLaw c*character (A i.1) c :=
      (Fintype.prod_sum (fun i : e × Fin h => fun c : (I → Binary) × (J → Binary) => channelLaw c*character (A i.1) c)).symm
    _ = _ := by
      simp_rw [Lax342547Proofs.ChannelCharacters.character_average]
      rw [Fintype.prod_prod_type]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_div_pow]
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const,one_pow]
      congr 1
      simp_rw [← pow_mul,Nat.mul_comm _ h]
      exact (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => h*(A i).rank) (2 : ℝ)).trans
        (by rw [← Finset.mul_sum])

/--
---
conclusion: Lax342547.TensorCharacters.product_tensor_characters
---
-/
theorem product_tensor_characters {e I J ι : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → e → Matrix I J Binary) (h : ℕ) (c : e × Fin h → (I → Binary) × (J → Binary)) :
    (∏ i, tensorCharacter h (A i) c) = tensorCharacter h (fun e => ∑ i, A i e) c := by
  classical
  unfold tensorCharacter
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact (Lax342547Proofs.ChannelCharacters.character_sum (fun i => A i j.1) (c j)).symm

end Lax342547Proofs.TensorCharacters
