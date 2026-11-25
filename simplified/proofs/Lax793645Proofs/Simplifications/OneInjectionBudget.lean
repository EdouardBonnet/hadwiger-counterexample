import Lax793645Proofs.Simplifications.OneInjectionTransfer
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RelativeInjectionBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The fixed price for all quadratic channel columns is absorbed by
the ambient size. It does not change the order of the construction constants. -/
theorem one_fire_budget (K : ℕ) (p : Shape) {l D : ℝ}
    (hD : 0≤D) (hh : 2*K+l+200*(D+2)≤2*p.h) :
    ∀ᶠ d : ℕ in atTop,
      bp (D*d)*(oneFireBill p (d/100) K (shine d)/
        (pushCost (bp (-l)) K)^(d/100))≤fringe d := by
  have he:=(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop ((2*(p.h:ℝ))^2+2+2*p.h*K))
  filter_upwards [he,eventually_ge_atTop 100] with d hd hk
  change (2*(p.h:ℝ))^2+2+2*p.h*K≤(d:ℝ) at hd
  let k:=d/100
  have ht : d≤200*k := by
    have h1 : 1≤d/100:=(Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hk)
    have hx:=Nat.div_add_mod' d 100
    unfold k
    omega
  have ht' : (d:ℝ)≤200*k:=by exact_mod_cast ht
  have h1 : (D+2)*d≤(2*p.h-(2*K+l))*k := by
    have h:=mul_le_mul_of_nonneg_left ht' (show 0≤D+2 by linarith)
    have h':=mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg k : 0≤(k:ℝ))
    linarith
  change bp _*(oneFireBill p k K (shine d)/_)≤_
  unfold oneFireBill oneChannelPrice pushCost shine fringe
  rw [←bp_sub,←bp_mul_nat,←bp_add,←bp_add,←bp_sub,←bp_add]
  apply bp_le
  nlinarith only [h1,hd,(Nat.cast_nonneg d : 0≤(d:ℝ))]

variable {p : Shape} {n N : ℕ}

theorem one_secure_pin_relative {E : OneUnit p n N×OneUnit p n N→Prop}
    {C U H l ε η : ℝ} (hE : named E C) (hF : named (E∘Prod.swap) C)
    (hU : 0<U) (hH : 0≤H) (hl : 0<l)
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (m : Mixer p n) (hc : oneBySide w m H)
    (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N)
    (K k : ℕ) (hP : ∀ x i e,dim (P x i e)≤K) (hB : ∀ x i e,dim (B x i e)≤K)
    (hx : ∀ x,w x≠0→∀ i,oneFrameLaw m (x i))
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) (h5 : 5≤N)
    (hmiss : (H/U)*bp (num (Row p n)+k+3-2*(N:ℝ))≤l)
    (hrel : 8*num (Comp p.g)*(3*l)≤ε)
    (habs : 8*num (Comp p.g)*(U+C*(oneFireBill p k K H/(pushCost l K)^k))≤η) :
    pr (pairW w w) (fun x=>E x ∧ ¬oneSecurePin P B x)≤ε*pr (pairW w w) E+η := by
  have hh:=one_secure_pin_bound hE hF hU hH hl w hw m hc P B K k hP hB hx hroom hN h5 hmiss
  have hv:=pr_nonneg (p:=E) (pairW_law hw hw).nz
  have hr:=mul_le_mul_of_nonneg_right hrel hv
  exact hh.trans (by nlinarith only [hr,habs])

end
end Lax793645Proofs.Simplifications
