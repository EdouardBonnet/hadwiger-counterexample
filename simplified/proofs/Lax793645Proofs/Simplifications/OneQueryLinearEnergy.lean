import Lax793645Proofs.Simplifications.OneLinearCellCaps
import Lax793645Proofs.Simplifications.QuadraticReferenceFourier
import Lax793645Proofs.Simplifications.OneQueryDensityRefinement
import Lax793645Proofs.Simplifications.LinearCellBounds
import Lax793645Proofs.Simplifications.FilteredProjectionBounds
import Lax793645Proofs.Simplifications.ColoredCutEnergy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I Y : Type} [Fintype I] [DecidableEq I] [Fintype Y] {p : Shape}

/-- The density energy on every bounded linear partition is uniformly
bounded. The bound is chosen before the number of linear equations. -/
theorem one_query_linear_energy_calendar (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c L : ℝ) (hL : 0<L) :
    ∃ B : ℝ,2≤B ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤L*unif x) →
      ∀ (q : I→F) (f : OneUnit p n (M*n)→Inputs p n I→Y),
      let K:=oneQueryReferenceSet v q (M*n); let ν:=unifOn K
      IsLaw ν ∧ ∀ r : ℕ,r≤R → ∀ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
      densityFamilyEnergy ν (colored π (prodW w) f)
        (coloredCutDensities ν (prodW w) f (oneTemplateCoordinates v) K) P.mulVec
        ≤num Y*B+1 ∧
      ∀ t : Wgt (OneUnit p n (M*n)×Y),(∀ i,0≤t i) →
        (∀ i,t i≤colored π (prodW w) f i) → ∀ x,
        let d:=mixW t (coloredCutDensities ν (prodW w) f (oneTemplateCoordinates v) K)
        0≤banner ν P.mulVec d x ∧ banner ν P.mulVec d x≤B+1 := by
  obtain ⟨B₀,hB₀,hcal⟩:=one_linear_cell_cap_calendar v M hM c L hL
  let B:=2*B₀
  have hB : 2≤B:=by dsimp only [B]; linarith only [hB₀]
  refine ⟨B,hB,fun R=>?_⟩
  let E:=crowded (ownPort v.t)
  let τ:=bp (-quadraticReferenceCost E)/2
  let δ:=bp (-(R:ℝ))/2
  have hτ : 0<τ:=half_pos (bp_pos _)
  have hδ : 0<δ:=half_pos (bp_pos _)
  have hM' : 0<(M:ℝ)/2:=by exact div_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)) (by norm_num)
  have hv : Tendsto (fun n : ℕ=>bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    convert (bp_tendsto_zero hM').comp tendsto_natCast_atTop_atTop using 1
    funext n
    congr 1
    push_cast
    ring
  have hb : Tendsto (fun n : ℕ=>2*bp (quadraticReferenceCost E)*bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    simpa using hv.const_mul (2*bp (quadraticReferenceCost E))
  have he : Tendsto (fun n : ℕ=>bp (R:ℝ)*bp (-10*n)/δ) atTop (nhds 0) := by
    simpa using (((bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp
      tendsto_natCast_atTop_atTop).const_mul (bp (R:ℝ))).div_const δ
  have he' : Tendsto (fun n : ℕ=>bp (-10*n)) atTop (nhds 0):=
    (bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hcal R,hv.eventually (eventually_le_nhds hτ),
    hb.eventually (eventually_le_nhds hδ),
    he.eventually (eventually_le_nhds zero_lt_one),he'.eventually (eventually_le_nhds hδ)]
    with n hn hnτ hnδ hne hne' m hN π hπ hcap w hw hz hinput q f K ν
  let Z:=geoMatrix (ownPort v.t) (ownMap v.t q)
  have hK : K=quadraticTraced E Z (N:=M*n) :=
    rfl
  obtain ⟨hν,hmass,hbias⟩:=quadratic_reference_bias E Z hnτ
  rw [←hK] at hν hmass hbias
  refine ⟨hν,fun r hr P=>?_⟩
  have hδr : δ≤bp (-num (Fin r))/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply bp_le
    simp only [num,Fintype.card_fin]
    exact neg_le_neg (by exact_mod_cast hr)
  have hs : stamina (mapW ν P.mulVec) δ := by
    have hh:=linear_cells_stamina ν hν (2*bp (quadraticReferenceCost E)*bp (-((M*n:ℕ):ℝ)/2))
      (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) hbias P (hnδ.trans hδr)
    exact fun a ha=>hδr.trans (hh a ha)
  have htail : ∀ a,pr π (fun o=>B*mapW ν P.mulVec a<
      pr (mapW (prodW w) (oneTemplateCoordinates v o)) (fun x=>K x ∧ P*ᵥx=a))≤bp (-10*n) := by
    intro a
    have hc:=linear_cell_reference_comparison ν hν
      (2*bp (quadraticReferenceCost E)*bp (-((M*n:ℕ):ℝ)/2))
      (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le)
      hbias P (hnδ.trans hδr) a
    refine (pr_mono hπ.nz (fun o ho=>?_)).trans
      (hn m (by omega) π hπ hcap (prodW w) hinput r hr P a)
    have hcut : pr (mapW (prodW w) (oneTemplateCoordinates v o))
        (fun x=>K x ∧ P*ᵥx=a) ≤
        pr (prodW w) (fun x=>P*ᵥoneTemplateCoordinates v o x=a) := by
      rw [mapW_pr]
      exact pr_mono (prodW_law hw).nz (fun x hx=>hx.2)
    have hm : B₀*mapW unif P.mulVec a≤B*mapW ν P.mulVec a := by
      calc
        _≤B₀*(2*mapW ν P.mulVec a):=
          mul_le_mul_of_nonneg_left hc (by linarith only [hB₀])
        _=_:=by dsimp only [B]; ring
    exact hm.trans_lt (ho.trans_le hcut)
  have henergy:=colored_cut_energy π hπ (prodW w) (prodW_law hw) f
    (oneTemplateCoordinates v) K ν hν (fun x hx=>uniform_on_support K x hx) P.mulVec
    B δ (bp (-10*n)) (by linarith) hδ hs htail
  have hcard : num (Vec (Fin r))≤bp (R:ℝ) := by
    rw [num,card_space,dim_vec]
    apply bp_le
    simpa only [Fintype.card_fin] using (show (r:ℝ)≤R from by exact_mod_cast hr)
  have herr : num (Vec (Fin r))*bp (-10*n)/δ≤1 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (bp_pos _).le) hδ.le).trans hne
  refine ⟨henergy.trans (add_le_add le_rfl herr),?_⟩
  exact filtered_cut_projection_bound π hπ (prodW w) (prodW_law hw) f
    (oneTemplateCoordinates v) K ν hν (fun x hx=>uniform_on_support K x hx)
    P.mulVec B δ (bp (-10*n)) (by linarith) hδ hne' hs htail

end
end Lax793645Proofs.Simplifications
