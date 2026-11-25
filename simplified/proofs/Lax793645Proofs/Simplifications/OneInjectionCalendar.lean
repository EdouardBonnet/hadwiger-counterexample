import Lax793645Proofs.Simplifications.OneInjectionBudget

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem eventually_double {P : ℕ→Prop} (h : ∀ᶠ d : ℕ in atTop,P d) :
    ∀ᶠ N : ℕ in atTop,P (2*N) := by
  obtain ⟨k,hk⟩:=eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop k] with N hN
  exact hk (2*N) (by omega)

set_option maxHeartbeats 1000000 in
/-- The single-frame injection producer is uniform for all compatible
pair events having the stated dictionary size, including rare events. -/
theorem one_guard_calendar (g K : ℕ) (D ε : ℝ) (hD : 0≤D) (hε : 0<ε) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g→p.h=h→
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
    ∀ (E : OneUnit p n N×OneUnit p n N→Prop),
    named E (bp (D*(2*N)))→named (E∘Prod.swap) (bp (D*(2*N)))→
    ∀ w (P : OnePrimalPinFamily p n N) (B : OneChannelPinFamily p n N) (m : Mixer p n),
    (∀ x i e,dim (P x i e)≤K)→(∀ x i e,dim (B x i e)≤K)→IsLaw w→
    oneBySide w m (shine (2*N))→(∀ x,w x≠0→∀ i,oneFrameLaw m (x i))→
    pr (pairW w w) (fun x=>E x ∧ ¬oneSecurePin P B x)≤
      ε*pr (pairW w w) E+edgeError (2*N) := by
  let W:=8*num (Comp g)
  obtain ⟨k,hk⟩ : ∃ k : ℕ,W*(3*bp (-(k:ℝ)))≤ε := by
    have ht : Tendsto (fun k : ℕ=>W*(3*bp (-(k:ℝ)))) atTop (𝓝 0) := by
      simpa using ((bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul 3).const_mul W
    obtain ⟨k,hk⟩:=(ht.eventually (gt_mem_nhds hε)).exists
    exact ⟨k,hk.le⟩
  let l:=bp (-(k:ℝ))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*K+(k:ℝ)+200*(D+2)))] with h hh p hg hp
  have hroomH : 2*K+(k:ℝ)+200*(D+2)≤2*p.h := by
    rw [hp]
    have hz : 0≤(h:ℝ):=Nat.cast_nonneg _
    linarith
  have hfire:=eventually_double (one_fire_budget K p hD hroomH)
  have hsmall : ∀ᶠ d : ℕ in atTop,
      8*num (Comp p.g)*(fringe d+fringe d)≤edgeError d := by
    filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.005:ℝ))
      (8*num (Comp p.g)*2) 0] with d hd
    unfold fringe edgeError
    rw [←two_mul,←mul_assoc]
    refine (mul_le_mul_of_nonneg_right
      (show _≤bp (0.005*d) from by simpa using hd.le) (bp_pos _).le).trans_eq ?_
    rw [←bp_add]
    congr 1
    ring
  have hsize:=eventually_double ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (10*((k:ℝ)+1))))
  filter_upwards [eventually_grid hfire,eventually_grid (eventually_double hsmall),
    columns_budget p (δ:=1) zero_lt_one 4 3 (by norm_num) (by norm_num),
    eventually_grid hsize] with M hM hT hS hY
  filter_upwards [hM,hT,eventually_ge_atTop 1,hY] with n hM hT hn hY
  dsimp only
  intro E hE hF w P B m hP hB hw hc hx
  let N:=M*n
  have hbase : 4*num (Full p n)+3≤N:=(hS n hn).trans_eq (one_mul _)
  have hcard : num (Full p n)=num (Row p n)+p.h := by
    simp [num,Full,Chan]
  have hN : Fintype.card (Row p n)+2*p.h+1≤N := by
    have hr : 0≤num (Row p n):=Nat.cast_nonneg _
    rw [hcard] at hbase
    have hh' : num (Row p n)+2*p.h+1≤N := by linarith
    exact_mod_cast hh'
  have h4 : 4*p.h+3≤N := by
    have hr : 0≤num (Row p n):=Nat.cast_nonneg _
    rw [hcard] at hbase
    have hh' : 4*(p.h:ℝ)+3≤N := by linarith
    exact_mod_cast hh'
  have h5 : 5≤N := by
    change 10*((k:ℝ)+1)≤(2*N:ℕ) at hY
    push_cast at hY
    have hk0 : 0≤(k:ℝ):=Nat.cast_nonneg _
    have hh' : (5:ℝ)≤N := by linarith
    exact_mod_cast hh'
  have hmiss : (shine (2*N)/fringe (2*N))*
      bp (num (Row p n)+(2*N/100:ℕ)+3-2*(N:ℝ))≤l := by
    have hq : 100*((2*N/100:ℕ):ℝ)≤2*N := by
      exact_mod_cast (Nat.mul_div_le (2*N) 100)
    unfold shine fringe l
    rw [←bp_sub,←bp_add]
    apply bp_le
    change 10*((k:ℝ)+1)≤(2*N:ℕ) at hY
    push_cast at hY ⊢
    linarith only [hY,hbase,hq,row_le p n]
  apply one_secure_pin_relative hE hF (bp_pos _) (bp_pos _).le (bp_pos _) w hw m hc
    P B K (2*N/100) hP hB hx hN h4 h5 hmiss ?_ ?_
  · change 8*num (Comp p.g)*(3*l)≤ε
    have heq : num (Comp p.g)=num (Comp g) := by cases hg; rfl
    rw [heq]
    exact hk
  · have ht:=mul_le_mul_of_nonneg_left (add_le_add_left hM (fringe (2*N)))
      (show 0≤8*num (Comp p.g) by unfold num; positivity)
    simpa only [N,shine,fringe,Nat.cast_mul,Nat.cast_ofNat,add_comm] using ht.trans hT

end
end Lax793645Proofs.Simplifications
