import Lax793645Proofs.Simplifications.OneInjectionTail
import Lax793645Proofs.Simplifications.NamedInjectionTransfer

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneBySide (w : Wgt (OneUnit p n N)) (m : Mixer p n) (H : ℝ) : Prop :=
  ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o

theorem one_by_side_on {w : Wgt (OneUnit p n N)} {m : Mixer p n} {H U : ℝ}
    (hw : SubLaw w) (h : oneBySide w m H) (S : OneUnit p n N→Prop)
    (hU : 0<U) (hS : U≤pr w S) : oneBySide (onW w S) m (H/U) := by
  intro i o
  refine (mapW_cap (on_mon hw.nz hU hS) (fun x=>x i) o).trans ?_
  have hh:=mul_le_mul_of_nonneg_left (h i o) (inv_nonneg.mpr hU.le)
  exact hh.trans_eq (by rw [div_eq_mul_inv]; ring)

theorem one_named_pin_fans {E : OneUnit p n N×OneUnit p n N→Prop}
    {C U H l : ℝ} (hE : named E C) (hU : 0<U) (hH : 0≤H) (hl : 0<l)
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (m : Mixer p n) (hc : oneBySide w m H)
    (P : OneUnit p n N→Space (Ray p n)) (B : OneUnit p n N→Space (Hyperbolic p.h))
    (K k : ℕ) (hP : ∀ x,dim (P x)≤K) (hB : ∀ x,dim (B x)≤K)
    (i j : Bool) (e : Comp p.g)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) (h5 : 5≤N)
    (hmiss : (H/U)*bp (num (Row p n)+k+3-2*(N:ℝ))≤l) :
    pr (pairW w w) (fun x=>E x ∧ rootFans (oneRoot P i e) (oneStrike B j e) x.1 x.2)≤
      3*l*pr (pairW w w) E+U+C*(oneFireBill p k K H/(pushCost l K)^k) := by
  refine named_fans_transfer _ hE hU hl ?_ w hw ?_
  · exact div_nonneg (mul_nonneg (mul_nonneg hH (bp_pos _).le) (bp_pos _).le)
      (pow_nonneg (div_nonneg hl.le (bp_pos _).le) _)
  intro S hS
  have hs:=one_by_side_on hw.sub hc S hU hS
  exact one_injection_tail P B K k hP hB (onW w S) w
    (on_law hw.nz (hU.trans_le hS)) hw m i j e (div_nonneg hH hU.le) hH hl
    (hs i) (hc j) hroom hN h5 hmiss

abbrev OnePrimalPinFamily (p : Shape) (n N : ℕ) :=
  OneUnit p n N→Bool→Comp p.g→Space (Ray p n)
abbrev OneChannelPinFamily (p : Shape) (n N : ℕ) :=
  OneUnit p n N→Bool→Comp p.g→Space (Hyperbolic p.h)

def oneAcceptsPin (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (x : OneUnit p n N×OneUnit p n N) :=onePinSafe (P x.1) (B x.2) x.1 x.2

def oneSecurePin (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (x : OneUnit p n N×OneUnit p n N) :=oneAcceptsPin P B x ∧ oneAcceptsPin P B x.swap

set_option maxHeartbeats 600000 in
/-- Endpoint injection fails on only a relative fraction of any pair
event with a bounded dictionary, plus the explicit absolute error. -/
theorem one_secure_pin_one {E : OneUnit p n N×OneUnit p n N→Prop}
    {C U H l : ℝ} (hE : named E C) (hU : 0<U) (hH : 0≤H) (hl : 0<l)
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (m : Mixer p n) (hc : oneBySide w m H)
    (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (K k : ℕ) (hP : ∀ x i e,dim (P x i e)≤K) (hB : ∀ x i e,dim (B x i e)≤K)
    (hx : ∀ x,w x≠0→∀ i,oneFrameLaw m (x i))
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) (h5 : 5≤N)
    (hmiss : (H/U)*bp (num (Row p n)+k+3-2*(N:ℝ))≤l) :
    pr (pairW w w) (fun x=>E x ∧ ¬oneAcceptsPin P B x)≤
      (4*num (Comp p.g))*(3*l*pr (pairW w w) E+U+
        C*(oneFireBill p k K H/(pushCost l K)^k)) := by
  classical
  let J:=Comp p.g×Bool×Bool
  let Q (a : J) (x : OneUnit p n N×OneUnit p n N):=
    E x ∧ rootFans (oneRoot (fun y=>P y a.2.1 a.1) a.2.1 a.1)
      (oneStrike (fun y=>B y a.2.2 a.1) a.2.2 a.1) x.1 x.2
  have hh x (h : pairW w w x≠0) (hf : E x ∧ ¬oneAcceptsPin P B x) : ∃ a,Q a x := by
    obtain ⟨e,i,j,v,hv,hn,hs⟩:=one_pin_failure_witness (P x.1) (B x.2) x.1 x.2 m
      (hx x.1 (left_ne_zero_of_mul h)) hf.2
    exact ⟨(e,i,j),hf.1,v,hv,hn,hs⟩
  have hw':=(pairW_law hw hw).nz
  refine ((pr_on_mono hw' hh).trans (pr_exists_le hw' Q)).trans ?_
  refine (Finset.sum_le_sum fun a _=>one_named_pin_fans hE hU hH hl w hw m hc
    (fun x=>P x a.2.1 a.1) (fun x=>B x a.2.2 a.1) K k (fun x=>hP x _ _)
    (fun x=>hB x _ _) a.2.1 a.2.2 a.1 hroom hN h5 hmiss).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,J,Fintype.card_prod,num,Fintype.card_bool]
  push_cast
  ring

theorem one_secure_pin_bound {E : OneUnit p n N×OneUnit p n N→Prop}
    {C U H l : ℝ} (hE : named E C) (hF : named (E∘Prod.swap) C)
    (hU : 0<U) (hH : 0≤H) (hl : 0<l)
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (m : Mixer p n) (hc : oneBySide w m H)
    (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (K k : ℕ) (hP : ∀ x i e,dim (P x i e)≤K) (hB : ∀ x i e,dim (B x i e)≤K)
    (hx : ∀ x,w x≠0→∀ i,oneFrameLaw m (x i))
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) (h5 : 5≤N)
    (hmiss : (H/U)*bp (num (Row p n)+k+3-2*(N:ℝ))≤l) :
    pr (pairW w w) (fun x=>E x ∧ ¬oneSecurePin P B x)≤
      (8*num (Comp p.g))*(3*l*pr (pairW w w) E+U+
        C*(oneFireBill p k K H/(pushCost l K)^k)) := by
  have ha:=one_secure_pin_one hE hU hH hl w hw m hc P B K k hP hB hx hroom hN h5 hmiss
  have hb:=one_secure_pin_one hF hU hH hl w hw m hc P B K k hP hB hx hroom hN h5 hmiss
  rw [perm_pair_prob] at hb
  have he : pr (pairW w w) (fun x=>E x ∧ ¬oneAcceptsPin P B x.swap)=
      pr (pairW w w) (fun x=>E x.swap ∧ ¬oneAcceptsPin P B x) := by
    rw [←perm_pair_prob w (fun x=>E x ∧ ¬oneAcceptsPin P B x.swap)]
    rfl
  have hm (x) : E x ∧ ¬oneSecurePin P B x→
      (E x ∧ ¬oneAcceptsPin P B x) ∨ (E x ∧ ¬oneAcceptsPin P B x.swap) := by
    unfold oneSecurePin
    tauto
  have hw':=(pairW_law hw hw).nz
  refine ((pr_mono hw' hm).trans ((pr_or_le hw').trans (add_le_add ha (he.trans_le hb)))).trans_eq ?_
  ring

end
end Lax793645Proofs.Simplifications
