import Lax793645Proofs.Simplifications.ConditionalCellHits
import Lax793645Proofs.Simplifications.QueryCoordinateLaws
import Lax793645Proofs.Simplifications.LinearCellBounds
import Lax793645Proofs.Simplifications.FilteredProjectionBounds

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
theorem query_linear_energy_calendar (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ B : ℝ,2≤B ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (π : Wgt (UnitType p n (M*n))),IsLaw π →
      (∀ o,π o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (w : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ (q : I→F) (f : UnitType p n (M*n)→Inputs p n I→Y),
      let K:=queryReferenceSet v q (M*n); let ν:=unifOn K
      IsLaw ν ∧ ∀ r : ℕ,r≤R → ∀ P : Mat (Fin r) (Fin (M*n)×Bool×KeySlots p v.t),
      densityFamilyEnergy ν (colored π (prodW w) f)
        (coloredCutDensities ν (prodW w) f (templateKeyCoordinates v) K) P.mulVec
        ≤num Y*B+1 ∧
      ∀ t : Wgt (UnitType p n (M*n)×Y),(∀ i,0≤t i) →
        (∀ i,t i≤colored π (prodW w) f i) → ∀ x,
        let d:=mixW t (coloredCutDensities ν (prodW w) f (templateKeyCoordinates v) K)
        0≤banner ν P.mulVec d x ∧ banner ν P.mulVec d x≤B+1 := by
  obtain ⟨B,α,hB,hα,hcal⟩:=coordinate_hit_calendar v M hM c
  refine ⟨B,hB,fun R=>?_⟩
  let E:=crowded (ownPort v.t)
  let τ:=bp (-num E)/2
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
  have hb : Tendsto (fun n : ℕ=>2*bp (num E)*bp (-((M*n:ℕ):ℝ)/2)) atTop (nhds 0) := by
    simpa using hv.const_mul (2*bp (num E))
  have ht : Tendsto (fun n : ℕ=>bp (-α*n)) atTop (nhds 0):=
    (bp_tendsto_zero hα).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ=>bp (R:ℝ)*bp (-10*n)/δ) atTop (nhds 0) := by
    simpa using (((bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp
      tendsto_natCast_atTop_atTop).const_mul (bp (R:ℝ))).div_const δ
  have he' : Tendsto (fun n : ℕ=>bp (-10*n)) atTop (nhds 0):=
    (bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hcal,hv.eventually (eventually_le_nhds hτ),
    hb.eventually (eventually_le_nhds hδ),
    ht.eventually (eventually_le_nhds (mul_pos hτ hδ)),
    he.eventually (eventually_le_nhds zero_lt_one),he'.eventually (eventually_le_nhds hδ)]
    with n hn hnτ hnδ hnt hne hne' m hN π hπ hcap w hw hz q f K ν
  let Z:=directions (ownPort v.t) (ownMap v.t q)
  have hK : K=gramKeySet E Z (M*n) :=
    funext fun x=>propext (query_gram_equivalence v.t q x)
  obtain ⟨hν,hmass,hbias⟩:=gram_reference_bias E Z hnτ
  rw [←hK] at hν hmass hbias
  refine ⟨hν,fun r hr P=>?_⟩
  have hδr : δ≤bp (-num (Fin r))/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply bp_le
    simp only [num,Fintype.card_fin]
    exact neg_le_neg (by exact_mod_cast hr)
  have hs : stamina (mapW ν P.mulVec) δ := by
    have hh:=linear_cells_stamina ν hν (2*bp (num E)*bp (-((M*n:ℕ):ℝ)/2))
      (mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le) hbias P (hnδ.trans hδr)
    exact fun a ha=>hδr.trans (hh a ha)
  have htail:=conditional_cell_hits π hπ (prodW w) (templateKeyCoordinates v) K P.mulVec
    B τ δ (bp (-α*n)) (bp (-10*n)) (by linarith) hτ hδ (bp_pos _).le
    hmass hnt hs (hn m hN π hπ hcap w hw hz)
  have henergy:=colored_cut_energy π hπ (prodW w) (prodW_law hw) f
    (templateKeyCoordinates v) K ν hν (fun x hx=>uniform_on_support K x hx) P.mulVec
    B δ (bp (-10*n)) (by linarith) hδ hs htail
  have hcard : num (Vec (Fin r))≤bp (R:ℝ) := by
    rw [num,card_space,dim_vec]
    apply bp_le
    simpa only [Fintype.card_fin] using (show (r:ℝ)≤R from by exact_mod_cast hr)
  have herr : num (Vec (Fin r))*bp (-10*n)/δ≤1 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (bp_pos _).le) hδ.le).trans hne
  refine ⟨henergy.trans (add_le_add le_rfl herr),?_⟩
  exact filtered_cut_projection_bound π hπ (prodW w) (prodW_law hw) f
    (templateKeyCoordinates v) K ν hν (fun x hx=>uniform_on_support K x hx)
    P.mulVec B δ (bp (-10*n)) (by linarith) hδ hne' hs htail

end
end Lax793645Proofs.Simplifications
