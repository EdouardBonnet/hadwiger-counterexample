import Lax793645Proofs.Simplifications.OnePreparationConditions
import Lax793645Proofs.Simplifications.OneLinearZeroDiscrepancy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PreliminaryRestrictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

theorem image_strength_slide {A C I : Type} [Fintype A] [Fintype C] [Fintype I]
    [DecidableEq I] {N c : ℕ} {X : A→C→Mat (Fin N) I} {cl : ImageClosure C I c}
    {s : ImageLeafMixture A C I N} {w μ : Wgt A} {D E ζ η : ℝ} {K L : ℕ}
    (h : s.strength X cl w μ D ζ K) (hD : D≤E) (hζ : ζ≤η) (hK : K≤L)
    (hμ : ∀ x,0≤μ x) : s.strength X cl w μ E η L := by
  refine ⟨h.part,fun i hi=>?_⟩
  have hh:=h.leaf i hi
  refine ⟨hh.pos,hh.fixpin,hh.closed,hh.bound.trans hK,fun b=>?_,fun x=>?_⟩
  · exact (hh.clear b).trans (bp_le (by gcongr))
  exact (hh.density x).trans (mul_le_mul_of_nonneg_right (bp_le (by gcongr)) (hμ x))

theorem one_upper_side {w v : Wgt (OneUnit p n N)} {m : Mixer p n} {L H L' : ℝ}
    (h : oneBySide w m L) (hc : ∀ x,v x≤H*w x) (hH : 0≤H) (hL : H*L≤L') :
    oneBySide v m L' := by
  intro i o
  refine (mapW_cap hc (fun x=>x i) o).trans ?_
  exact (mul_le_mul_of_nonneg_left (h i o) hH).trans
    (by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hL (one_raw_nonneg m o))

theorem one_sap_twice {w : Wgt (OneUnit p n N)} {s : OneLeafMixture p n N}
    (hw : IsLaw w) (hs : (1/2:ℝ)≤s.amount w) (x) : s.sap w x≤2*w x :=
  (on_mon hw.nz (by norm_num) hs x).trans_eq (by norm_num)

theorem one_potency {w : Wgt (OneUnit p n N)} {s : OneLeafMixture p n N}
    (hw : IsLaw w) (hs : (1/2:ℝ)≤s.amount w) (P : OneUnit p n N→Prop)
    (hP : pollen≤pr (s.sap w) P) (x) : onW (s.sap w) P x≤bp 100*w x := by
  have hv:=ImageLeafMixture.sap_law (lt_of_lt_of_le (by norm_num) hs) hw
  calc
    _≤pollen⁻¹*s.sap w x:=on_mon hv.nz pollen_pos hP x
    _≤pollen⁻¹*(2*w x):=mul_le_mul_of_nonneg_left (one_sap_twice hw hs x)
      (inv_nonneg.mpr pollen_pos.le)
    _≤bp 100*w x:=by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right pollen_price (hw.nz x)

def oneIntern (q : PreparationParameters) (p : Shape) (n N : ℕ):=
  ∀ m : Mixer p n,OnePhaseReady p n N (mstep q.rank) ((2*N)/denomStep q.rank)
    q.rank q.k q.d m (tinyPhase p.g q.rank q.spJoint) coin warn
    (heatloss q.rank q.k) q.spear (bp (q.spJoint*(2*N)))

/-- The preparation schedule records only bounds already supplied by the
one-frame counting, closed-pin, phase, and injection calendars. -/
structure OnePlanted (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  early : OnePreparationAllows q
  hM : 1≤M
  hg : Odd p.g
  hG : 3≤p.g
  hJ : 1≤p.j
  hR : 1≤p.r
  hB : (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j)
  exactRoom : 4*oneScreenRank p q.e+2*q.e*p.r<p.g*p.r
  wrap : ∀ᶠ n : ℕ in atTop,let N:=M*n;
    2*dim (OneFull p n)+3≤N ∧ 4≤N ∧
    (3*(onePreparationCover q):ℝ)*(2*N)≤((q.u:ℝ)-1)*(2*N) ∧
    (∀ (m : Mixer p n) (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)),
      (onePinClosure p n).close a.sp=a.sp →
      pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
        fee (2*N) ((q.ζ/6)/4) (imagePlanRank a.sp)) ∧
    oneIntern q p n N ∧ oneOutside q p n N

theorem OnePlanted.unary_room {q : PreparationParameters} (h : OnePlanted q p M) :
    ∀ᶠ n : ℕ in atTop,Fintype.card (Row p n)+2*p.h+3≤M*n := by
  filter_upwards [h.wrap] with n hn
  have hr:=hn.1
  rw [one_full_dimension] at hr
  omega

end
end Lax793645Proofs.Simplifications
