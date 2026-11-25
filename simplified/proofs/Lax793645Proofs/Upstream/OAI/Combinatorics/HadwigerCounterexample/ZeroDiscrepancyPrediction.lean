/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyPrediction.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.NumericalGramPrescriptions

namespace Lax793645Proofs.Upstream.OAI

/-! # Zero Discrepancy Prediction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open Lax793645Proofs.Simplifications
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def screenRank (p : Shape) (K : ℕ) := (tagDegree p.g)*(p.h+2*p.J*K)
def screen (p : Shape) (i : Orient p n N) (s : Label p.b) (E : Finset (Tag p.g)) (r : ℕ)
    (g : Augur p N) (δ : ℝ) :=
  ∃ w : Pdual p n,
    (∀ l f,pr (spins p n) (mismatch p g w l s f i) ≤ δ)∧
    ∀ l : Tag p.g,
    ∃ M:Moment p n,M.rank ≤ r ∧ ∀ x : Knobs p.g n,
      let f:= Flavor.full
      let v:=spring p l s f x
      cleanInput p E x → w (useAtom p l s f x)=dialed p l f x+evmat M v v

set_option maxHeartbeats 600000 in
theorem coreRole (p : Shape) (U : Profile p n) (E : Finset (Tag p.g))
    (α : F) (hg : Odd p.g)
    (h : ∀ t,t∉E → role p n U+sharedT p n t U+α=1)
    (l s x) (hc : cleanInput p E x) :
    let f:= Flavor.full
    let M:=useAtom p l s f x
    T0 p n U M + α*role p n M=dialed p l f x := by
  classical
  intro f M
  let Q:= scan p l f x
  have h1 : Q (.inr ())=0 := clean_scan _ x hc l _ (by simp [retainedProbe])
  have hq : role p n M=dialed p l f x := by
    rw [role_scan]
    change Q.diagO=Q.sumBit; unfold Digest.sumBit; rw [h1,add_zero]
  have hh t : sharedT p n t M=0 := by rw [sharedT_scan p hg]; change Q _+(if l=t then Q _ else 0)=_
                                           ; rw [h1]; simp
  have he t (ht : t∈ E) : roleT p n t M=0 := by
    rw [roleT_scan p]
    refine sum_eq_zero fun i _ => ?_
    exact clean_scan _ x hc l (.inl (i,t)) (by simpa [retainedProbe] using ht)
  have hl t (hE : t∉E) : role p n U+sharedT p n t U+α=1 := h t hE
  rw [T0_val]; change role _ _ U* _ + _ + _ = _
  simp_rw [hh,mul_zero,zero_add]
  rw [←hq]
  let r := role p n U
  have hm : role p n M=∑ t, roleT p n t M := by unfold role; rw [LinearMap.sum_apply]
  rw [hm,mul_sum,mul_sum,←sum_add_distrib,←sum_add_distrib]
  refine Finset.sum_congr rfl fun t _=>?_
  by_cases ht : t∈E
  · rw [he t ht]; ring
  rw [← add_mul,←add_mul,hl t ht,one_mul]

theorem inner_gem (p : Shape) (x : UnitType p n N) (i : Bool) (t : Tag p.g) :
    ∃ M : Moment p n,M.rank ≤ (tagDegree p.g)*p.h ∧ ∀ (s z),
      innerP p x i (atom p t s z)=mpair M (mom p s z) := by
  classical
  let A:=onSide x i; let B:=onSide x (!i)
  let P (e : Comp p.g) := channel (B e).2*(channel (B e).1)ᵀ
  let Z (e : Comp p.g) := liftM (primary (A e).1)ᵀ (primary (A e).2)ᵀ (P e)
  let M := ∑ i:TagStar t,Z i.val
  have ht i : (Z i).rank ≤ p.h := (rank_lift_le ..).trans ((Matrix.rank_mul_le_left ..).trans
    ((Matrix.rank_le_card_width (channel (B i).2)).trans_eq (by simp)))
  refine ⟨M,(mrk_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>ht i.val)).trans_eq ?_),?_⟩
  · simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,card_star]
  intro s z
  change (∑ i:Comp p.g, mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)))
    =_
  let Q:= mom p s z
  have he i :
      mpair (P i) (liftM (primary (A i).1) (primary (A i).2) (atom p t s z i)) =
      if inc i t then mpair (Z i) Q else 0 := by
    rw [mpair_liftM,atom_def]; by_cases ht:inc i t <;> simp only [ht,ite_false,ite_true,map_zero]; rfl
  simp_rw [he]
  unfold M; rw [←Finset.sum_filter,mpair_sum]; exact Finset.sum_subtype _ (by simp) _

theorem zero_screen (p : Shape) (x : UnitType p n N) (i : Bool) (s : Label p.b)
    (m : Mixer p n) (α : F) (hg : Odd p.g)
    (U : Profile p n) (E : Finset (Tag p.g))
    (h : ∀ t,t∉E → role p n U+sharedT p n t U+α=1)
    (K : ℕ) (hk : totalRank U ≤ K) (g : Augur p N)
    (δ : ℝ) (L : Finset (Label p.b)) (hs : s∉ L)
    (hz : postulates p (onSide x i) g (yoke p m x i U α) L δ) :
    screen p (onSide x i) s E (screenRank p K) g δ := by
  classical
  let a := U; let f:=Flavor.full (g:=p.g)
  refine ⟨_,hz s hs,fun l=>?_⟩
  obtain ⟨M,hM,ht⟩:=inner_gem p x i l
  refine ⟨M+qmix m a l,le_trans (mrk_add_le ..) ?_,fun y hy=>?_⟩
  · refine (Nat.add_le_add hM (qmix_rank ..)).trans ?_
    unfold screenRank; change _+p.J*(tagDegree p.g)*(2*totalRank a)≤_
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*(tagDegree p.g))
      (Nat.mul_le_mul_left 2 hk)) _) (le_of_eq (by ring))
  let A:=useAtom p l s f y
  let z:=lit f l y; let T:=mom p s z
  have h0 : (Tsym m a+α • role p n) A= dialed p l f y+mpair (qmix m a l) T := by
    have hh : Tmix m a A=mpair (qmix m a l) T := Tmix_atom ..
    change T0 p n a A + Tmix m a A + α * role p n A=_
    rw [hh,add_right_comm]
    exact congrArg (·+_) (coreRole p U E α hg h l s y hy)
  change innerP p x i A + (Tsym m a + α • role p n) A = dialed p l f y+_
  rw [show innerP p x i A=mpair M T from ht s z,h0, ←mpair_outer,mpair_add]
  change mpair M T+(dialed p l f y + _) = dialed p l f y+(mpair M T+_)
  rw [add_left_comm]; rfl
end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
