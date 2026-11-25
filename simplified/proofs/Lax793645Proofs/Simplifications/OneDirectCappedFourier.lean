import Lax793645Proofs.Simplifications.OneDirectMomentDecay
import Lax793645Proofs.Simplifications.OneQueryWeightSupremum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem fourier_weight_character {J : Type} [Fintype J] [DecidableEq J]
    (f w : Wgt (Vec J)) (b : ℝ) (hw : fourierNorm w≤b) :
    ∃ ξ,|avg unif (fun x=>f x*w x)|≤b*|linearFourier f ξ| := by
  obtain ⟨ξ,_,hξ⟩:=Finset.exists_max_image univ
    (fun ξ:Vec J=>|linearFourier f ξ|) Finset.univ_nonempty
  refine ⟨ξ,?_⟩
  rw [linear_fourier_pair]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul]
  calc
    _≤∑ ζ:Vec J,|linearFourier f ξ| * |linearFourier w ζ|:=
      Finset.sum_le_sum (fun ζ _=>mul_le_mul_of_nonneg_right
        (hξ ζ (Finset.mem_univ _)) (abs_nonneg _))
    _=fourierNorm w*|linearFourier f ξ|:=by rw [←Finset.mul_sum,mul_comm]; rfl
    _≤_:=mul_le_mul_of_nonneg_right hw (abs_nonneg _)

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def inputCharacter (ξ : Vec (I×Block p.g×Fin n)) (x : Inputs p n I) : ℝ:=
  vectorPhase ξ ((inputCoordinates p n I).symm x)

omit [DecidableEq I] in
theorem input_character_abs (ξ : Vec (I×Block p.g×Fin n)) (x : Inputs p n I) :
    |inputCharacter ξ x|=1:=wsign_abs _

theorem one_query_weight_character (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (b ε : ℝ) (o : OneUnit p n N) (h : oneQueryWeightBad v D ψ b ε o) :
    ∃ ξ : Vec (I×Block p.g×Fin n),
      ε<b*|oneQueryCorrelation v D (fun x=>ψ x*inputCharacter ξ x) o| := by
  obtain ⟨w,hw,he⟩:=h
  obtain ⟨ξ,hξ⟩:=fourier_weight_character
    (fun x=>D (oneTemplateCoordinates v o (inputCoordinates p n I x))*ψ (inputCoordinates p n I x))
    (fun x=>w (inputCoordinates p n I x)) b hw
  rw [input_average (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w x)] at hξ
  refine ⟨ξ,he.trans_le (hξ.trans_eq ?_)⟩
  congr 2
  unfold linearFourier oneQueryCorrelation
  rw [←input_average (fun x=>D (oneTemplateCoordinates v o x)*(ψ x*inputCharacter ξ x))]
  apply avg_congr
  intro x _
  simp only [inputCharacter,LinearEquiv.symm_apply_apply]
  ring

/-- A finite character union gives uniform control of orientation-dependent
Fourier-bounded weights. No U² quantity occurs. -/
theorem one_direct_capped_leaf_fourier (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c b ε : ℝ) (hb : 0≤b) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n→
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M*n))),
      (∀ o,0≤π o)→(∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw mixer (M*n) o)→
      (∀ x,|D x|≤1)→(∀ x,D x≠0 → oneOwnPart v.t q x)→
      (∀ ξ,|linearFourier D ξ|≤δ)→(∀ x,|ψ x|≤1)→
      pr π (oneQueryWeightBad v D ψ b ε)≤bp (-(n:ℝ)) := by
  obtain ⟨s,hs,hdecay⟩:=one_direct_moment_decay v M hM
  obtain ⟨k,hk⟩:=(bp_poly_dom_nat (a:=1) (by norm_num) (b/ε) 0).exists
  have hbk : b≤ε*bp (k:ℝ):=by
    have hh : b/ε≤bp (k:ℝ):=by simpa only [pow_zero,mul_one,one_mul] using hk.le
    exact ((div_le_iff₀ hε).mp hh).trans_eq (mul_comm _ _)
  let R:=num I*num (Block p.g)
  let H:=max c 0*(M:ℝ)+R+(k:ℝ)+1
  have hH : 0≤H:=by dsimp only [H,R]; positivity
  obtain ⟨δ,hδ,hdecay⟩:=hdecay H hH
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hdecay] with n hn mixer hN q D ψ π hπ hcap hD hsup hF hψ
  let l:=2*(n/(2*s))
  let μ:=oneUnitRaw mixer (M*n)
  let χ (ξ : Vec (I×Block p.g×Fin n)) (x : Inputs p n I):=ψ x*inputCharacter ξ x
  let bad (ξ : Vec (I×Block p.g×Fin n)) (o : OneUnit p n (M*n)):=
    ε<b*|oneQueryCorrelation v D (χ ξ) o|
  have hraw ξ : avg μ (fun o=>|oneQueryCorrelation v D (χ ξ) o|^l)≤bp (-H*n):=by
    apply hn.2 mixer hN q D (χ ξ) hD hsup hF
    intro x
    dsimp only [χ]
    rw [abs_mul,input_character_abs,mul_one]
    exact hψ x
  have hbound ξ : ε^l*pr π (bad ξ)≤bp (c*(M*n:ℕ))*b^l*bp (-H*n):=by
    have hpoint o : ε^l*ind (bad ξ o)≤b^l*|oneQueryCorrelation v D (χ ξ) o|^l:=by
      by_cases ho : bad ξ o
      · rw [ind_one ho,mul_one,←mul_pow]
        exact pow_le_pow_left₀ hε.le ho.le l
      · rw [ind_zero ho,mul_zero]
        positivity
    rw [pr,←avg_mul']
    refine (avg_mono hπ hpoint).trans ?_
    have hcap' : avg π (fun o=>b^l*|oneQueryCorrelation v D (χ ξ) o|^l)≤
        bp (c*(M*n:ℕ))*b^l*avg μ (fun o=>|oneQueryCorrelation v D (χ ξ) o|^l):=by
      unfold avg
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro o _
      exact (mul_le_mul_of_nonneg_right (hcap o) (by positivity)).trans_eq (by ring)
    exact hcap'.trans (mul_le_mul_of_nonneg_left (hraw ξ)
      (mul_nonneg (bp_pos _).le (pow_nonneg hb _)))
  have hsum : pr π (oneQueryWeightBad v D ψ b ε)≤∑ ξ,pr π (bad ξ):=
    (pr_mono hπ (fun o ho=>one_query_weight_character v D ψ b ε o ho)).trans (pr_exists_le hπ bad)
  have hbpow : b^l≤ε^l*bp ((k:ℝ)*l):=by
    simpa only [mul_pow,←bp_mul_nat] using pow_le_pow_left₀ hb hbk l
  have hln : (l:ℝ)≤n:=by
    have hh:=Nat.div_mul_le_self n (2*s)
    have hh' : l*s≤n:=by simpa only [l,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
    exact_mod_cast ((Nat.le_mul_of_pos_right l hs).trans hh')
  have hexp : R*n+c*(M*n:ℕ)+(k:ℝ)*l-H*n≤-(n:ℝ):=by
    have hc:=mul_le_mul_of_nonneg_right (le_max_left c 0) (Nat.cast_nonneg (M*n) : (0:ℝ)≤(M*n:ℕ))
    have hl:=mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg k : (0:ℝ)≤k)
    simp only [Nat.cast_mul,H] at hc ⊢
    linarith only [hc,hl]
  apply le_of_mul_le_mul_left (a:=ε^l) _ (pow_pos hε l)
  refine (mul_le_mul_of_nonneg_left hsum (pow_nonneg hε.le l)).trans ?_
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum (fun ξ _=>hbound ξ)).trans ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,dim_vec]
  have hcard : (Fintype.card (I×Block p.g×Fin n):ℝ)=R*n:=by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,R,num]
    ring
  rw [hcard]
  have hp : 0≤bp (R*n)*bp (c*(M*n:ℕ))*bp (-H*n):=
    mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) (bp_pos _).le
  have hh:=mul_le_mul_of_nonneg_left hbpow hp
  have heq : bp (R*n)*(bp (c*(M*n:ℕ))*b^l*bp (-H*n))=
      (bp (R*n)*bp (c*(M*n:ℕ))*bp (-H*n))*b^l:=by ring
  rw [heq]
  refine hh.trans ?_
  have heq' : (bp (R*n)*bp (c*(M*n:ℕ))*bp (-H*n))*(ε^l*bp ((k:ℝ)*l))=
      ε^l*bp (R*n+c*(M*n:ℕ)+(k:ℝ)*l-H*n):=by
    simp only [sub_eq_add_neg,bp_add,neg_mul]
    ring
  rw [heq']
  exact mul_le_mul_of_nonneg_left (bp_le hexp) (pow_nonneg hε.le l)

end
end Lax793645Proofs.Simplifications
