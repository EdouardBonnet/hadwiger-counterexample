import Lax793645Proofs.Simplifications.OnePreparationBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
/-- All hypotheses of one-frame preparation are produced in the order
channels, fixed shape, ambient multiplier, and sample parameter. -/
theorem one_preparation_calendar (q : PreparationParameters) (g : ℕ)
    (hq : OnePreparationAllows q) (hk : q.k≤q.d)
    (hK : q.spJoint+1≤0.49*q.k)
    (hu : 3*onePreparationCover q+1≤q.u) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g → p.h=h →
      Odd p.g → 3≤p.g → 1≤p.j → 1≤p.r →
      (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j) →
      4*oneScreenRank p q.e+2*q.e*p.r<p.g*p.r →
      ∀ᶠ M : ℕ in atTop,OnePlanted q p M := by
  have hL : 0≤q.spear:=mul_nonneg (bp_pos _).le hq.hL
  have hD : 0≤q.spJoint:=by unfold spJoint; positivity
  filter_upwards [one_phase_calendar g q.rank q.k q.d q.spJoint q.spear hL hD hk hK,
    one_outside_calendar q g] with h hphase hguard p hg hh hodd hG hJ hR hB hexact
  filter_upwards [hphase p hg hh,hguard p hg hh,eventually_ge_atTop 1,
    columns_budget p (δ:=1) zero_lt_one 4 5 (by norm_num) (by norm_num),
    columns_budget p (δ:=q.ζ/12) (div_pos hq.pos (by norm_num)) 4 5 (by norm_num) (by norm_num)]
    with M hphase hguard hM hcols hsmall
  refine ⟨hq,hM,hodd,hG,hJ,hR,hB,hexact,?_⟩
  filter_upwards [hphase,hguard,eventually_ge_atTop 1]
    with n hphase hguard hn
  let N:=M*n
  have hcols:=hcols n hn
  have hsmall:=hsmall n hn
  rw [one_mul] at hcols
  have hdim : num (Full p n)=num (Row p n)+p.h:=by simp [num,Full]
  rw [hdim] at hcols hsmall
  have hrow : 0≤num (Row p n):=by unfold num; positivity
  have hh0 : 0≤(p.h:ℝ):=Nat.cast_nonneg _
  have hroom : 2*dim (OneFull p n)+3≤N := by
    rw [one_full_dimension]
    have hr : 2*(num (Row p n)+2*p.h)+3≤N:=by linarith only [hcols,hrow]
    exact_mod_cast hr
  have h4 : 4≤N := by
    have hr : (4:ℝ)≤N:=by linarith only [hcols,hrow,hh0]
    exact_mod_cast hr
  have hfee : (dim (OneFull p n):ℝ)+2≤((q.ζ/6)/4)*(2*N) := by
    rw [one_full_dimension]
    push_cast
    change num (Row p n)+2*p.h+2≤_
    linarith only [hsmall,hrow,hh0]
  have hureal : (3:ℝ)*onePreparationCover q+1≤q.u:=by exact_mod_cast hu
  have hrecord := mul_le_mul_of_nonneg_right
    (show (3:ℝ)*onePreparationCover q≤(q.u:ℝ)-1 by linarith only [hureal])
    (show (0:ℝ)≤2*N by positivity)
  exact ⟨hroom,h4,hrecord,fun m a ha=>one_closed_pin_cap m a ha
    (by linarith only [hq.small]) hroom hfee,(by simpa only [oneIntern,hg] using hphase),hguard⟩

end
end Lax793645Proofs.Simplifications
