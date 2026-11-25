import Lax793645Proofs.Simplifications.ReducedMixerExistence
import Lax793645Proofs.Simplifications.OneParameterExistence
import Lax793645Proofs.Simplifications.OneFinalContradiction
import Lax793645Proofs.Simplifications.OneGraphLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerMatching.Main

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Filter Finset PreparationParameters
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneConstruction
variable {p:Shape} {n N M s0:ℕ} {b:PreparationParameters}

def conflictLowerBound (m:Mixer p n) (N:ℕ) (b:PreparationParameters):=
  ∀ w:Wgt (OneUnit p n N),OneNascent b m w →
    carried w (fun x=>(oneRawHoles m).unit (x true,x false)) →
    bp (-200*(2*N:ℝ))≤pr (pairW w w) (oneClash m)

theorem eventual_conflict_lower_bound (h:OneParameters.Complete p M b s0):
    ∀ᶠ n:ℕ in atTop,∀ m:Mixer p n,unaryGood m (onePreparationPins b) s0 →
      reducedBinaryGood m → conflictLowerBound m (M*n) b := by
  classical
  let P (n:ℕ):=∃ m:Mixer p n,unaryGood m (onePreparationPins b) s0 ∧ reducedBinaryGood m ∧
    ∃ w:Wgt (OneUnit p n (M*n)),OneNascent b m w ∧
      carried w (fun x=>(oneRawHoles m).unit (x true,x false)) ∧ oneConflicted m w
  suffices hf:¬∃ᶠ n:ℕ in atTop,P n by
    refine (not_frequently.mp hf).mono (fun n hn m hm hb w hw hu=>?_)
    by_contra! hbad
    exact hn ⟨m,hm,hb,w,hw,hu,hbad⟩
  intro hfreq
  haveI:=frequently_iff_neBot.mp hfreq
  let l:Filter ℕ:=atTop⊓principal {n|P n}
  have hl:l≤atTop:=inf_le_left
  have hP:∀ᶠ n in l,P n:=
    (show ∀ᶠ n in principal {i|P i},P n from eventually_principal.mpr (fun _ h=>h)).filter_mono inf_le_right
  let (n:ℕ):Nonempty (Mixer p n):=⟨⟨0,0,0⟩⟩
  obtain ⟨m,hm⟩:=taking hP
  obtain ⟨w,hw⟩:=taking (hm.mono fun n hn=>hn.2.2)
  have hF:∀ᶠ n in l,∃ s:OneLeafMixture p n (M*n),OneEntered b (m n) (w n) s:=by
    filter_upwards [hw,h.initial.filter_mono hl] with n hn hi
    exact hi _ _ hn.1 hn.2.1
  obtain ⟨s,hs⟩:=taking hF
  obtain ⟨k,hprep⟩:=one_finite_preparation h.planted
  apply one_refute_finite_preparation h.toOneAnalyticParameters hl
    ((hm.and hw).mono fun _ ⟨ha,hb⟩=>⟨hb.1,ha.1,ha.2.1,hb.2.2⟩) (k:=k)
  filter_upwards [hprep.filter_mono hl,hw,hs] with n hp hw hs
  exact hp _ _ _ hw.1 hs

open HadwigerMatching LinearListHadwiger

/-- The original graph conclusion, using a single quadratic frame at
each component, affine selectors, and linear query partitions. -/
theorem exists_graphs (lower:ℕ):∃ m:ℕ,max lower 5 ≤ m ∧
    ∃ G:SimpleGraph (Fin m),G.indepNum≤2 ∧
      (connectedMatchingNumber G:ℚ)<(m:ℚ)/100 := by
  classical
  obtain ⟨p,b,M,s0,h,_,hD,hL⟩:=OneParameters.exists_parameters
  let B:=4*num (Comp p.g)
  have htrend: Tendsto (fun n:ℕ=>2*(M*n)) atTop atTop:=
    (one_trend_sizes atTop le_rfl h.planted.hM).1
  have hgood:=goodReducedMixers p (onePreparationPins b) s0 h.planted.hG h.planted.hg
    h.planted.hJ (by have hh:=h.unary.profiles; omega) h.mixerRoom
  have hall:∀ᶠ n:ℕ in atTop,∃ m:ℕ,max lower 5 ≤ m ∧
      ∃ G:SimpleGraph (Fin m),G.indepNum≤2 ∧
        (connectedMatchingNumber G:ℚ)<(m:ℚ)/100 := by
    filter_upwards [eventual_conflict_lower_bound h,h.planted.wrap,hgood,
      htrend.eventually (transfer_scales (g:=2) (by decide)
        (show 0≤B from by unfold B num; positivity)),
      ((tendsto_ord (g:=2) (by decide)).comp htrend).eventually
        (eventually_ge_atTop (max lower 5))] with n hsat hroom hmix htransfer hlarge
    let N:=M*n
    obtain ⟨m,hum,hbm⟩:=hmix
    have hconf:=hsat m hum hbm
    have hframe:Fintype.card (Row p n)+2*p.h+1≤N:=by
      have hh:=hroom.1
      rw [one_full_dimension] at hh
      omega
    have hcard:(Fintype.card (OneOrient p n N×OneOrient p n N):ℝ)≤bp (B*(2*N:ℝ)^2):=by
      rw [one_pair_card]
      apply bp_le
      have hh:(dim (OneFull p n):ℝ)≤N:=by
        exact_mod_cast (show dim (OneFull p n)≤N by have hh:=hroom.1; omega)
      have hz:0≤4*num (Comp p.g):=by unfold num; positivity
      have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hz)
        (Nat.cast_nonneg (α:=ℝ) N)
      unfold B
      nlinarith only [hc,mul_nonneg hz (sq_nonneg (N:ℝ))]
    obtain ⟨x,hx,hmatching⟩:=htransfer (OneOrient p n N) (oneRawHoles m) (oneRaw m N)
      (one_raw_law m hframe) (by simpa only [N,Nat.cast_mul,Nat.cast_ofNat] using hcard) (by
        intro w hw hcaps hunit
        let E:=onePairEquiv p n N
        have hc:pairCaps (oneRaw m N) b.L (bp ((b.D:ℝ)*(2*N))) w:=by
          rw [hD,hL]
          convert hcaps using 1 <;> dsimp only [N] <;> norm_num <;> congr 2 <;> push_cast <;> ring
        have hborn:=one_pair_nascent b m w hw hc
        have hsupport:carried (mapW w E)
            (fun x=>(oneRawHoles m).unit (x true,x false)):=
          mapW_carried hunit (fun x hx=>hx)
        have hh:=hconf _ hborn hsupport
        rw [one_pair_conflict] at hh
        convert hh using 1 <;> norm_num <;> congr 1 <;> push_cast <;> ring)
    exact ⟨ord 2 (2*N),hlarge,(oneRawHoles m).graph x,hx,hmatching⟩
  exact hall.exists.elim (fun _ hn=>hn)

end OneConstruction
end
end Lax793645Proofs.Simplifications
