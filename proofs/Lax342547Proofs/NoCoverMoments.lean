import Lax342547.NoCoverMoments
import Lax342547Proofs.ComponentMoments
import Lax342547Proofs.IndexedRankGrowth

namespace Lax342547Proofs.NoCoverMoments
open Lax342547.NoCoverMoments

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters Lax342547.TensorCharacters Lax342547.ComponentSpaces
open Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.NoCoverMoments.sum_matrix_rank
---
-/
theorem sum_matrix_rank {I J ι : Type} [Fintype I] [Fintype J] [Fintype ι]
    (A : ι → Matrix I J Binary) :
    Module.finrank Binary (LinearMap.range (∑ i, (A i).mulVecLin)) = (∑ i, A i).rank := by
  have hs : (∑ i, A i).mulVecLin = ∑ i, (A i).mulVecLin := by
    apply LinearMap.ext
    intro v
    simp only [Matrix.mulVecLin_apply,LinearMap.sum_apply,Matrix.sum_mulVec]
  unfold Matrix.rank
  rw [hs]

/--
---
conclusion: Lax342547.NoCoverMoments.no_cover_even_moment
---
-/
theorem no_cover_even_moment {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k)
    (hcover : ∀ S : Submodule Binary (e → I → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → J → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p) :
    (∑ c, productLaw (fun _ : e × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (A x) c|^(2*t)) ≤
      (4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))) := by
  classical
  let m := 100*r+10
  let R := (2 : ℕ)^(k-(100*r+12))
  let ρ := productLaw (fun _ : Fin (2*t) => μ)
  let rank := fun sample : Fin (2*t) → Ω => ∑ i, (∑ j, A (sample j) i).rank
  have hprob := Lax342547Proofs.FiniteSampling.product_probability (fun _ : Fin (2*t) => μ) (fun _ => hμ)
  have hmoment := Lax342547Proofs.ComponentMoments.component_even_moment_bound μ A ψ h t hμ.1 hψ
  have hsplit := Lax342547Proofs.MomentTails.rank_moment_split ρ rank h R hprob
  have hbad : cellMass ρ (fun sample => rank sample < R) ≤ (4 : ℝ)^(2*t)*p^(2^(k-m)) := by
    have hg := Lax342547Proofs.IndexedRankGrowth.component_no_cover_rank_indexed (ι := Fin (2*t)) μ
      (fun x i => (A x i).mulVecLin) r k p hμ hp0 hp1 hr hA (by omega) (by simpa only [Fintype.card_fin] using hsize)
      (by
        intro S T hS hT hdS hdT
        apply hcover S T hS hT
        · simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using hdS
        · simpa only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using hdT)
    have hpow : (2 : ℝ)^(k-m)/4 = (R : ℝ) := by
      dsimp [R,m]
      have he : k-(100*r+10) = (k-(100*r+12))+2 := by omega
      rw [he,pow_add]
      norm_num
    have hevent : (fun sample : Fin (2*t) → Ω => rank sample < R) =
        (fun sample => ((∑ i, Module.finrank Binary (LinearMap.range (∑ j : Fin (2*t), (A (sample j) i).mulVecLin))) : ℝ) <
          (2^(k-(100*r+10)) : ℝ)/4) := by
      funext sample
      apply propext
      simp_rw [sum_matrix_rank]
      rw [hpow]
      rw [← Nat.cast_sum]
      change rank sample < R ↔ (rank sample : ℝ) < (R : ℝ)
      exact_mod_cast (Iff.rfl : rank sample < R ↔ rank sample < R)
    simpa only [ρ,hevent,m,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] using hg
  exact hmoment.trans (hsplit.trans (add_le_add hbad le_rfl))

/--
---
conclusion: Lax342547.NoCoverMoments.no_cover_phase_tail
---
-/
theorem no_cover_phase_tail {e I J Ω : Type} [Fintype e] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (r h t k : ℕ) (p θ : ℝ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (hA : ∀ x, ∑ i, (A x i).rank ≤ r) (hψ : ∀ x, |ψ x| ≤ 1)
    (hsize : 2*t = 2^k) (hk : 100*r+12 ≤ k)
    (hcover : ∀ S : Submodule Binary (e → I → Binary),
      ∀ T : Submodule Binary (Module.Dual Binary (e → J → Binary)),
      Componentwise S → DualComponentwise T →
      (Module.finrank Binary S : ℝ) ≤ (r : ℝ)*(2*t) →
      (Module.finrank Binary T : ℝ) ≤ (r : ℝ)*(2*t) →
      cellMass μ (fun x => projection (LinearMap.piMap (fun i => (A x i).mulVecLin)) S T = 0) ≤ p)
    (hθ : 0 < θ) :
    cellMass (productLaw (fun _ : e × Fin h => channelLaw))
      (fun c => θ ≤ |∑ x, μ x*ψ x*tensorCharacter h (A x) c|) ≤
      ((4 : ℝ)^(2*t)*p^(2^(k-(100*r+10)))+1/(2 : ℝ)^(h*2^(k-(100*r+12))))/θ^(2*t) := by
  classical
  have hprob := Lax342547Proofs.FiniteSampling.product_probability
    (fun _ : e × Fin h => (channelLaw (I := I) (J := J))) (fun _ => Lax342547Proofs.ChannelCharacters.channel_probability)
  exact (Lax342547Proofs.MomentTails.finite_moment_markov _ _ θ (2*t) hprob.1 hθ).trans
    (div_le_div_of_nonneg_right
      (no_cover_even_moment μ A ψ r h t k p hμ hp0 hp1 hr hA hψ hsize hk hcover) (by positivity))

end Lax342547Proofs.NoCoverMoments
