import Lax793645Proofs.Simplifications.OnePhaseBudgets
import Lax793645Proofs.Simplifications.OneRawImageCalendar

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000 in
/-- The phase alternative has a consistent parameter schedule for the
actual quadratic-frame law. No phase estimate is an external input. -/
theorem one_phase_calendar (g r k d : ℕ) (D L : ℝ) (hl : 0≤L) (hd : 0≤D)
    (hk : k≤d) (hK : D+1≤0.49*k) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g→p.h=h→
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ mix : Mixer p n,OnePhaseReady p n N (mstep r) ((2*N)/denomStep r) r k d mix
        (tinyPhase g r D) coin warn (heatloss r k) L (bp (D*(2*N))) := by
  filter_upwards [one_glimpses_stage g k r d D L,tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (2*pcoef g r D))] with h hstage hH p hg hp
  subst g h
  let ε:=heatloss r k
  let t:=tinyPhase p.g r D
  let A:=rhUp L t
  let B:=rhUp A coin
  obtain ⟨hG,hY⟩:=hstage p rfl rfl
  have he : ∀ᶠ V : ℕ in atTop,oneGlimpseBill p k A+bp (-0.1*V)<coin^(k+1) ∧
      5*coin+bp (-0.24*V)<0.005 ∧
      (2*num (Comp p.g)*L)*bp (-0.4*V)≤t/2 := by
    have ht:=tinyPhase_pos p.g r D
    have hf1 : ∀ᶠ V : ℕ in atTop,bp (-0.1*V)<coin^(k+1)-oneGlimpseBill p k A:=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (sub_pos.mpr hG))
    have hf2 : ∀ᶠ V : ℕ in atTop,bp (-0.24*V)<0.005-5*coin:=
      (bp_nat_vanish (by norm_num)).eventually (gt_mem_nhds (by norm_num [coin]))
    have hf3 : ∀ᶠ V : ℕ in atTop,(2*num (Comp p.g)*L)*bp (-0.4*V)<t/2 := by
      have hh : Tendsto (fun V : ℕ=>(2*num (Comp p.g)*L)*bp (-0.4*V)) atTop (𝓝 0) := by
        simpa using (bp_nat_vanish (by norm_num : 0<(0.4:ℝ))).const_mul (2*num (Comp p.g)*L)
      exact hh.eventually (gt_mem_nhds (half_pos ht))
    filter_upwards [hf1,hf2,hf3] with V h1 h2 h3
    exact ⟨by linarith,by linarith,h3.le⟩
  have hε : 0<ε:=heatloss_pos r k
  have hε6 : ε≤6 := by
    unfold ε heatloss
    rw [div_le_iff₀ (by positivity)]
    have hr : 0≤(r:ℝ):=Nat.cast_nonneg _
    have hk : 0≤(k:ℝ):=Nat.cast_nonneg _
    linarith
  filter_upwards [columns_budget p (δ:=0.004) (by norm_num)
    (2*(r:ℝ)) (4*p.h*(2*(r:ℝ)+k)) (by positivity) (by positivity),
    columns_budget p (δ:=1) zero_lt_one 4 5 (by norm_num) (by norm_num),
    one_raw_image_calendar p hε hε6,
    eventually_grid (eventually_double he),
    eventually_grid (eventually_double (one_limit_pow p r hd hH)),
    eventually_grid (eventually_double (one_atlas_stage p r)),
    eventually_grid (eventually_double (one_early_spend A)),
    eventually_grid (eventually_double (one_early_spend B)),
    eventually_grid (eventually_double (one_early_spend (t/2)⁻¹)),
    eventually_grid (eventually_double (eventually_ge_atTop (denomStep r)))]
    with M hcols hfull hraw hδ hF hQ ha hb hu hN
  filter_upwards [eventually_ge_atTop 1,hraw,hδ,hF,hQ,ha,hb,hu,hN]
    with n hn hz hz' hA hZ hα hβ hInv ht
  dsimp only
  intro mix
  let N:=M*n
  have h1 : 2*(r:ℝ)*num (Full p n)+4*p.h*(2*(r:ℝ)+k)≤0.004*(2*N) := by
    have hh:=hcols n hn
    have hN0 : 0≤(N:ℝ):=Nat.cast_nonneg _
    linarith
  have h2 : 4*num (Full p n)+5≤N:=by simpa only [one_mul] using hfull n hn
  let b:=(2*N)/denomStep r
  refine {
    hb := (Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using ht)
    hm := by unfold mstep; omega
    hk := hk
    hc := tinyPhase_pos ..
    hc' := tinyPhase_le _ _ hd
    hl := by norm_num [coin]
    hl' := by norm_num [coin]
    hψ := bp_pos _
    hL := hl
    hH := (bp_pos _).le
    hroom := hz.1
    hN := hz.2.1
    hchannels := hz.2.2.1
    cap := hz.2.2.2 mix
    noBranch := ?_
    frames := ?_
    atlas := fun T hT=>by
      simpa only [oneCoverDimension,Nat.cast_mul,Nat.cast_ofNat] using hZ T hT
    price := ?_
    price' := ?_
    localQ := ?_
    testFailure := ?_
    testFailure' := hY
    beatSlack := ?_ }
  · simpa only [oneNoSweepBudget,oneNoSweepActual,Nat.cast_mul,Nat.cast_ofNat] using hA
  · refine le_trans ?_ hz'.2.2
    unfold oneScaleBill
    have he:=(span_stage b r (2*N) (Nat.mul_div_le _ _)).1
    have hx : num (Row p n)+(2*maxSpan (mstep r) b r:ℕ)+3-2*(N:ℝ)≤ -0.4*(2*N) := by
      push_cast at he ⊢
      have h5 : (5:ℝ)≤N:=by exact_mod_cast hz.2.1
      linarith only [row_le p n,h2,he,h5]
    exact mul_le_mul_of_nonneg_left (bp_le (by
      simpa only [N,b,Nat.cast_mul,Nat.cast_ofNat] using hx)) (by unfold num; positivity)
  · intro x y hx hy
    exact one_price_bound x y (by omega) (by omega) h1 (by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hα)
  · intro x y hx hy
    exact one_price_bound x y (by omega) (by omega) h1 (by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hβ)
  · intro x hx
    let H:=bp (D*(2*N))
    have hh : rhUp H t*oneHeatRate p n N ε x k≤H*loseA p (2*N) x k := by
      unfold rhUp
      rw [mul_comm _ H,mul_assoc]
      exact mul_le_mul_of_nonneg_left (one_price_bound x k (by omega) (by omega) h1
        (by simpa only [N,Nat.cast_mul,Nat.cast_ofNat] using hInv)) (bp_pos _).le
    change bp _*bp _*_≤_
    refine (mul_le_mul_of_nonneg_left hh (mul_nonneg (bp_pos _).le (bp_pos _).le)).trans ?_
    unfold H loseA
    rw [←bp_add,←bp_add,←bp_add]
    apply bp_le
    have h3:=mul_le_mul_of_nonneg_right hK (show 0≤2*(N:ℝ) by positivity)
    simp only [N,Nat.cast_mul,Nat.cast_ofNat] at h3 ⊢
    have hN0 : 0≤(M:ℝ)*n:=by positivity
    linarith only [h3,hN0]
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz'.1
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz'.2.1

end
end Lax793645Proofs.Simplifications
