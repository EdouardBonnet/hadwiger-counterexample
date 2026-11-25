import Lax793645Proofs.Simplifications.LinearScreenContradiction
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyLemma

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module Filter
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Bounded linear predictors give consistency directly on the prepared
mixed law. The two endpoints need not be independent. Their exceptional
rank masses are charged to their original marginals, without leaf conditioning. -/
theorem linear_silicon_calendar (p : Shape)
    (M K D q B : ℕ)
    (hD : (p.g-1)/2+2*D≤q) (hg : 8*D<p.g*p.g)
    (hB : B<Fintype.card (Label p.b))
    (hj : 1≤p.j) (hg' : Odd p.g) (hr : 1≤p.r)
    (hs : 2*screenRank p K+1≤privateWidth p.g*(p.g-q)*p.r) (L : ℝ) :
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ n : ℕ in atTop,
      let N:=M*n; let U:=UnitType p n N
      ∀ m : Mixer p n,2*num (Full p n)<N →
      ∀ (w : Wgt U) (α : Bool→F) (g : Bool→Augur p N) (R : ℕ),
        8*p.g*R≤n → (∀ i,LinearAugur (g i) R) → IsLaw w → bySide p w m L →
      (∀ x,w x≠0 → joins x≤2*D ∧ ∃ (v : Bool→Profile p n) (H : Bool→Finset (Label p.b)),
        (∀ i,(H i).card≤B ∧ v i∈Xspace p n ∧ totalRank (v i)≤K ∧ frameLaw m (onSide x i)) ∧
          Uembed x.1 (v true)=Uembed x.2 (v false) ∧ claimed p x g m v α H ε) →
        α true=α false := by
  classical
  have h3 : 3≤p.g := by
    by_contra! h
    have he : p.g=1:=by obtain ⟨r,hr⟩:=hg'; omega
    simp [he,privateWidth] at hs
  let a:=fiddleRate p (Hue (2*screenRank p K+1))
  have ha : 0≤a:=mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (labFee_pos ..).le)
  let c:=(p.g:ℝ)*(a+4)
  have hc : 0<c:=mul_pos (by exact_mod_cast (show 0<p.g by omega)) (by linarith)
  let ε:=(2*c)⁻¹
  have hε : 0<ε:=by positivity
  have hcap : ∀ᶠ n : ℕ in atTop,L≤bp ((n:ℝ)/32) := by
    have hh:=expO_const (tendsto_natCast_atTop_atTop (R:=ℝ)) L (1/32) (by norm_num)
    exact hh.mono fun n hn=>(le_abs_self L).trans
      (by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hn)
  refine ⟨ε,hε,?_⟩
  filter_upwards [prepared_growing_linear_rank_calendar p,hcap,eventually_ge_atTop (2*p.r),
    eventually_ge_atTop 5] with n hn hL hn' hn5 N U m hN w α g R hR hlin hw hside hclaimed
  choose H hdim φ hφ using fun i=>joint_predictor_coordinates (g i) R (hlin i)
  have hdim' (i : Bool) : dim (H i)≤n/4 := by
    have h1:=Nat.mul_le_mul_left 4 (hdim i)
    have h2 : 4*(p.g*R)≤n:=by nlinarith only [hR]
    omega
  have hN' : 2*num (Full p n)-(N:ℝ)≤-1 := by
    have hh : 2*Fintype.card (Full p n)<N:=by exact_mod_cast hN
    have hh' : 2*Fintype.card (Full p n)+1≤N:=by omega
    have hh'' : 2*num (Full p n)+1≤(N:ℝ):=by exact_mod_cast hh'
    linarith only [hh'']
  let Bad (i : Bool) (o : Orient p n N) := ∃ s : Label p.b,
    ¬Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp (H i).subtype)
  have hbad (i : Bool) : pr w (fun x=>Bad i (onSide x i))≤bp (-(n:ℝ)/2) := by
    rw [←mapW_pr w (fun x=>onSide x i) (Bad i)]
    apply hn N m hN' (H i) (hdim' i) (mapW w (fun x=>onSide x i))
    intro o
    exact (hside i o).trans (mul_le_mul_of_nonneg_right hL (raw_nonneg m o))
  let AllBad (x : U):=∃ i,Bad i (onSide x i)
  have hbad' : pr w AllBad≤2*bp (-(n:ℝ)/2) := by
    exact (pr_exists_le hw.nz _).trans ((Finset.sum_le_sum fun i _=>hbad i).trans_eq
      (by simp only [Finset.sum_const,card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat]))
  have hsmall : 2*bp (-(n:ℝ)/2)<1 := by
    have hh : (5:ℝ)≤n:=by exact_mod_cast hn5
    calc
      _=bp (1-(n:ℝ)/2):=by rw [bp_sub,bp_one,neg_div,bp_neg]; ring
      _<bp 0:=bp_lt (by linarith only [hh])
      _=1:=bp_zero
  have hgood : 0<pr w (fun x=>¬AllBad x) := by
    rw [pr_not,hw.total]
    linarith only [hbad',hsmall]
  obtain ⟨x,hx,hwx⟩:=exists_of_pr_pos hw.nz hgood
  by_contra he
  obtain ⟨hd,v,T,hv,hshare,hclaim⟩:=hclaimed x hwx.ne'
  obtain ⟨s,E,hE,i,hi⟩:=unit_screen p K D q B hD hg h3 hB m x hg' hj v α he
    (fun i=>(hv i).2) hd hshare T (fun i=>(hv i).1) g ε hclaim
  have hfree : Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) (onSide x i)).comp
      (H i).subtype) := by
    by_contra hh
    exact hx ⟨i,s,hh⟩
  let : Fintype (H i):=Fintype.ofInjective
    (fun x : H i=>(x.val : PairedKeys (Comp p.g) (Fin N))) Subtype.val_injective
  let : Fintype (Module.Dual F (H i)):=Fintype.ofInjective
    (fun f : Module.Dual F (H i)=>(f : H i→F)) DFunLike.coe_injective
  have hroom : 2*screenRank p K+1≤privateWidth p.g*(p.g-E.card)*p.r:=
    hs.trans (by gcongr)
  have hgap:=linear_screen_gap (H i) (onSide x i) s hfree (g i) (φ i) (hφ i) E
    (screenRank p K) ε m hj hr hg' hn' hroom hi
  change 1≤c*ε at hgap
  have heq : c*ε=(1/2:ℝ):=by unfold ε; field_simp
  rw [heq] at hgap
  norm_num at hgap

end
end Lax793645Proofs.Simplifications
