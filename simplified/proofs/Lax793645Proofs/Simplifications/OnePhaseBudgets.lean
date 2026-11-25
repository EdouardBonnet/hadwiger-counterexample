/- Numerical estimates for the quadratic-frame phase alternative.
Adapted from the vendored Apache-2.0 OpenAI PhaseParameters module. -/
import Lax793645Proofs.Simplifications.OneFinitePhaseAlternative
import Lax793645Proofs.Simplifications.OneInjectionCalendar
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PhaseParameters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneNoSweepActual (p : Shape) (N m b r : ℕ) (c ψ H : ℝ):=
  bp (2*(r:ℝ)*num (Comp p.g)*N)*(H*oneCubePrice p^2*
    (exponentErr p m b c/ψ^(2^m*(2*b))))

theorem one_absorb_pow (p : Shape) {D : ℝ} (hD : 0≤D) (r b N : ℕ)
    (hN : N ≤2*denomStep r*b)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    exponentErr p (mstep r) b (tinyPhase p.g r D)/warn^(2^(mstep r)*(2*b))
      ≤ 2*bp (-(stage p.g r D)*N) := by
  let Z := pcoef p.g r D
  let L := stage p.g r D
  let s := 2^(mstep r)*(2*b)
  have hl : 0 ≤ L := by unfold L stage num; positivity
  have hx : 12*(s:ℝ)+L*N ≤ Z*b := by
    have h : (N:ℝ) ≤ 2*(denomStep r:ℝ)*b := by exact_mod_cast hN
    have hs : (s:ℝ)=(Bstep r:ℝ)*b := by unfold s Bstep; push_cast; ring
    unfold Z pcoef; rw [hs]; change _ ≤ (12*_+2*_ * L)*_
    nlinarith only [mul_le_mul_of_nonneg_left h hl]
  have hz : L*N+10*(s:ℝ) ≤ (p.h:ℝ)*b/2 := by
    have hb : 2*Z*(b:ℝ) ≤ (p.h:ℝ)*b :=
      mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    linarith [(Nat.cast_nonneg s : 0≤(s:ℝ))]
  unfold exponentErr tinyPhase warn
  change (((2:ℝ)^s*2^s)*bp (-Z)^b+bp _)/bp (-10)^s≤_
  rw [←bp_nat s,←bp_mul_nat,←bp_mul_nat, ← bp_add,←bp_add,add_div,← bp_sub,← bp_sub,
    two_mul]
  refine add_le_add (bp_le ?_) (bp_le ?_)
  · change _ ≤ -L*N; linarith only [hx]
  change _ ≤ -L*N; linarith only [hz]

theorem one_limit_pow (p : Shape) (r : ℕ) {D : ℝ} (hD : 0≤D)
    (hp : 2*pcoef p.g r D ≤ p.h) :
    ∀ᶠ N : ℕ in atTop,warn + oneNoSweepActual p N (mstep r) (N/denomStep r) r
      (tinyPhase p.g r D) warn (bp (D*N))<0.005 := by
  let C := oneCubePrice p
  have hw : warn < 0.005 := by
    unfold warn; rw [bp_neg, show (10:ℝ)=↑(10:ℕ) from by norm_num, bp_nat]; norm_num
  have hi : Tendsto (fun N : ℕ => warn+(2*C^2)*bp (-1*N)) atTop (𝓝 warn) := by
    have h := (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul (2*C^2)
    simpa only [neg_mul,mul_zero,add_zero] using h.const_add warn
  filter_upwards [hi.eventually (gt_mem_nhds hw),eventually_ge_atTop (denomStep r)]
    with N h hN
  let b := N / denomStep r
  have he : N≤2*denomStep r*b := by
    have h' : 1≤b := (Nat.le_div_iff_mul_le (denom_pos r)).mpr (by simpa using hN)
    have h2 : b*denomStep r + N%denomStep r=N := Nat.div_add_mod' ..
    have h3 : N%denomStep r < denomStep r := Nat.mod_lt _ (denom_pos r)
    nlinarith
  have hh : oneNoSweepActual p N (mstep r) b r (tinyPhase p.g r D) warn (bp (D*N))≤
      2*C^2*bp (-1*N) := by
    let A := bp (2*(r:ℝ)*num (Comp p.g)*N)
    unfold oneNoSweepActual
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (one_absorb_pow p hD r b N he hp)
      (mul_nonneg (bp_pos _).le (sq_nonneg _)
      )) (bp_pos _).le).trans_eq ?_
    change A * (bp _ * C^2 * _) = _
    have he : A * bp (D*N) * bp (-(stage p.g r D)*N)= bp (-1*N) := by
      unfold A stage; rw [←bp_add,←bp_add]; congr 1; ring
    rw [← he]; ring
  exact (add_le_add_right hh _).trans_lt h

theorem one_atlas_stage (p : Shape) (r : ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ T : SymCover p N,((∑ e,dim (T e))≤2*maxSpan (mstep r) (N/denomStep r) r) →
      num (SymAtlas p r T)≤bp (0.002*N) := by
  let K := num (SymWidths p r)
  let L := bp (num (Comp p.g)*r*r)
  have he := bp_poly_dom_nat (by norm_num : 0<(0.001:ℝ)) (K*L) 0
  filter_upwards [he] with N h T hT
  apply (sym_atlas_size T _).trans
  let W := maxSpan (mstep r) (N/denomStep r) r
  have hf : ((∑ e,dim (T e):ℕ):ℝ)≤2*W := by exact_mod_cast hT
  have h1 := mul_le_mul_of_nonneg_right hf (show 0≤(r:ℝ) from Nat.cast_nonneg _)
  have hL : ((∑ e,dim (T e):ℕ):ℝ)*r≤0.001*N := h1.trans
    (span_stage _ r N (Nat.mul_div_le _ _)).2
  have h2 : K*L≤bp (0.001*N) := by simpa using h.le
  have h3 : 0≤K := Nat.cast_nonneg _
  rw [bp_add]
  change K * (_ * L) ≤ _
  rw [mul_comm _ L, ←mul_assoc]
  exact (mul_le_mul h2 (bp_le hL) (bp_pos _).le (bp_pos _).le).trans_eq (by
    rw [←bp_add]; congr 1; ring)

theorem one_price_bound {p : Shape} {r n N k : ℕ} {L : ℝ}
    (x y : ℕ) (hx : x≤ 2*r) (hy : y≤ 2*r+k)
    (hf : (2*(r:ℝ))*num (Full p n)+4*p.h*(2*(r:ℝ)+k) ≤ 0.004*(2*N))
    (hl : L ≤ bp (0.004*(2*N))) :
    L*oneHeatRate p n N (heatloss r k) x y≤loseA p (2*N) x y := by
  apply (mul_le_mul_of_nonneg_right hl
    (mul_nonneg (bp_pos _).le (bp_pos _).le)
    ).trans
  unfold loseA
  rw [←bp_add,←bp_add]
  refine bp_le ?_
  let ε := heatloss r k
  have he : ε*(4*r+k + (1:ℝ))=0.001 := by
    unfold ε heatloss; field_simp
  have hg : (x:ℝ)≤ 2*r := by exact_mod_cast hx
  have hh : (y:ℝ)≤ 2*r+k := by exact_mod_cast hy
  have ht : ε*(x+y:ℝ) ≤ 0.001 := he ▸ mul_le_mul_of_nonneg_left
    (show _≤_ by linarith) (heatloss_pos r k).le
  have hN := mul_le_mul_of_nonneg_right ht (show 0≤(2*(N:ℝ)) by positivity)
  have hi :
      num (Row p n)*x+4*p.h*(y:ℝ) ≤ 0.004*(2*N) := by
    have hu := mul_le_mul (row_le p n) hg
      (Nat.cast_nonneg x : 0≤(x:ℝ)) (Nat.cast_nonneg _ : 0≤num (Full p n))
    have hv := mul_le_mul_of_nonneg_left hh (show 0≤ 2*(p.h:ℝ) by positivity)
    linarith only [hf,hu,hv]
  push_cast
  unfold ε at hN
  linarith [(show 0≤(2*(N:ℝ)) by positivity)]

theorem one_early_spend (W : ℝ) :
    ∀ᶠ N : ℕ in atTop,W≤bp (0.004*N) := by
  filter_upwards [bp_poly_dom_nat (by norm_num : 0<(0.004:ℝ)) W 0] with N h
  simpa using h.le

theorem one_glimpses_stage (g k r d : ℕ) (D L : ℝ) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
      oneGlimpseBill p k (rhUp L (tinyPhase g r D)) < coin^(k+1) ∧
      2*oneGlimpseBill p d (rhUp L (tinyPhase g r D))≤coin/2 := by
  let L' := rhUp L (tinyPhase g r D)
  let f (k h : ℕ) := (num (Comp g))*(L'*2*bp ((k:ℝ)-h))
  have ht k : Tendsto (f k) atTop (𝓝 0) := by
    let c : ℝ := num (Comp g)*L'*2*bp k
    have h : f k=fun h : ℕ => c*bp (-1*h) := by
      unfold f c; ext; simp [neg_mul,bp_sub,bp_neg]; ring
    rw [h]
    simpa using (bp_nat_vanish (by norm_num : 0<(1:ℝ))).const_mul c
  have hh : 0<coin := by norm_num [coin]
  filter_upwards [(ht k).eventually (gt_mem_nhds (pow_pos hh (k+1))),
    (ht d).eventually (gt_mem_nhds (show 0<coin/4 by linarith))] with h hA hB p hg hp
  subst g h
  change f k p.h<coin^(k+1) ∧ 2*f d p.h ≤ coin/2
  exact ⟨hA,by linarith only [show f d p.h<coin/4 from hB]⟩


end
end Lax793645Proofs.Simplifications
