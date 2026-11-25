import Lax793645Proofs.Simplifications.OneQueryMomentDecay
import Lax793645Proofs.Simplifications.OneQueryWeightSupremum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniform Fourier comparison under any exponentially capped leaf. The
exceptional event quantifies over all input weights after the orientation
is known. The key test and nominal phase are fixed before that draw. -/
theorem one_capped_leaf_fourier {I : Type} [Fintype I] [DecidableEq I]
    {p : Shape} (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c b ε : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3 ≤ M*n →
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
      (∀ o,0≤π o) → (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw mixer (M*n) o) →
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → oneOwnPart v.t q x) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      pr π (oneQueryWeightBad v D ψ b ε)≤bp (-(n:ℝ)) := by
  obtain ⟨s,hs,hdecay⟩:=one_query_moment_decay v M hM
  obtain ⟨k,hk⟩:=(bp_poly_dom_nat (a:=1) (by norm_num) (b/ε) 0).exists
  have hbk : b≤ε*bp (k:ℝ):=by
    have hh : b/ε≤bp (k:ℝ):=by simpa only [pow_zero,mul_one,one_mul] using hk.le
    exact ((div_le_iff₀ hε).mp hh).trans_eq (mul_comm _ _)
  let H:=max c 0*(M:ℝ)+4*(k:ℝ)+1
  have hH : 0≤H:=by dsimp only [H]; positivity
  obtain ⟨δ,hδ,hdecay⟩:=hdecay H hH
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hdecay] with n hn mixer hN q D ψ π hπ hcap hD hsup hF hψ
  let μ:=oneUnitRaw mixer (M*n)
  let l:=n/s
  have hm:=one_query_uniform_weight_moment v D ψ μ π b (bp (c*(M*n:ℕ))) ε hπ hcap hb hε.le l
  have hraw:=hn.2 mixer hN q D ψ hD hsup hF hψ
  have hbpow : b^(4*l)≤ε^(4*l)*bp (4*(k:ℝ)*l):=by
    have hh:=pow_le_pow_left₀ hb hbk (4*l)
    rw [mul_pow,←bp_mul_nat] at hh
    exact hh.trans_eq (by congr 1; congr 1; push_cast; ring)
  have hln : (l:ℝ)≤n:=by exact_mod_cast Nat.div_le_self n s
  have he : c*(M*n:ℕ)+4*(k:ℝ)*l-H*n≤-(n:ℝ):=by
    have hc:=mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg (M*n) : (0:ℝ)≤(M*n:ℕ))
    have hl:=mul_le_mul_of_nonneg_left hln (show 0≤4*(k:ℝ) by positivity)
    simp only [Nat.cast_mul,H] at hc ⊢
    linarith only [hc,hl]
  have hbound : bp (c*(M*n:ℕ))*b^(4*l)*avg μ (fun o=>(oneQueryFourth v D ψ o)^l)≤
      ε^(4*l)*bp (-(n:ℝ)):=by
    refine (mul_le_mul_of_nonneg_left hraw
      (mul_nonneg (bp_pos _).le (pow_nonneg hb _))).trans ?_
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbpow (bp_pos (c*(M*n:ℕ))).le) (bp_pos (-H*n)).le
    refine hh.trans ?_
    have heq : bp (c*(M*n:ℕ))*(ε^(4*l)*bp (4*(k:ℝ)*l))*bp (-H*n)=
        ε^(4*l)*bp (c*(M*n:ℕ)+4*(k:ℝ)*l-H*n):=by
      simp only [sub_eq_add_neg,bp_add,neg_mul]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (bp_le he) (pow_nonneg hε.le _)
  exact le_of_mul_le_mul_left (hm.trans hbound) (pow_pos hε (4*l))

end
end Lax793645Proofs.Simplifications
