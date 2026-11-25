import Lax793645Proofs.Simplifications.OnePredictedTableCompatibility
import Lax793645Proofs.Simplifications.OnePredictedFiles

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneStation StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Finset Matrix Function LinearMap
open scoped BigOperators
noncomputable section
namespace OneOptions
variable {p : Shape} {n N M s0 : ℕ} {b : PreparationParameters}

theorem prepared_claimed (c : PredictionClass) (α : Party) (hc : c.lit α)
    (g : Bool → OneAugur p N) (m : Mixer p n) (z : OneMarks p n N)
    (o : OneUnit p n N) (L : Stalls p) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ ε) (hclaim : oneClaimed o g m (z o) α L δ)
    (hexact : c=dusk → oneExactInk m z o) :
    oneClaimed o (onePreparedPredictor c g) m (z o) α L ε := by
  classical
  by_cases hd : c=dusk
  · have ha := dusk_lit α (hd ▸ hc)
    intro i a ha' l f
    have he (y : Knobs p.g n) :
        ¬oneMismatch (onePreparedPredictor c g i) (oneYoke m o i (z o i) (α i)) l a f (o i) y := by
      intro hbad
      apply hbad
      rw [ha]
      exact (hexact hd i _ (mem_useAtom ..)).trans (by simp [onePreparedPredictor,hd])
    change pr (spins p n) (oneMismatch (onePreparedPredictor c g i)
      (oneYoke m o i (z o i) (α i)) l a f (o i))≤ε
    have hz : oneMismatch (onePreparedPredictor c g i)
        (oneYoke m o i (z o i) (α i)) l a f (o i)=(fun _=>False):=
      funext fun y=>eq_false (he y)
    rw [hz,pr_false]
    exact hε
  · simpa only [onePreparedPredictor,if_neg hd] using
      (show oneClaimed o g m (z o) α L ε from fun i a ha l f => (hclaim i a ha l f).trans hδ)

set_option maxHeartbeats 1500000 in
theorem predicted_file_coverage (x : OneSketch p M) (s : OneLeafMixture p n (M*n))
    (v : OneStation p n (M*n) (onePreparationPins b) s) (m : cycleM p) (U : Wgt (OneUnit p n (M*n)))
    (hv : v.bank) (h : OneLead U s (m n) b.leafNew (2*b.ζ) (onePreparationPins b)) (hE : OneAnalyticParameters p M b s0)
    (hmarks : s.within (fun o => oneSeems b (m n) s o (fun i => x.g i n)
      (x.m n o) (x.L n o) x.α (x.ε n) ∧ glint p (x.m n o)=x.r ∧
      (x.c=dusk → oneExactInk (m n) (x.m n) o)))
    {η ε : ℝ} {R : ℕ}
    (hclass : oneFiniteClass (fun i=>x.g i n) x.α=x.c)
    (hrows : OneAlgebraicRows (fun i=>x.g i n) R)
    (hcells : ∀ l q k, η≤oneWisp p (onePredictorPartition x.c (fun i=>x.g i n)) l q
      (onePredictorPartition x.c (fun i=>x.g i n) l q k))
    (hε : 0 ≤ ε) (hε' : x.ε n ≤ ε)
    (hN : 2*num (Toast p)-((M*n:ℕ):ℝ) ≤ -1)
    (hcal : ∀ f : PredictedFile p (onePreparationPins b),
      ∀ Y : OneSilhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ oneWisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η)
    (i j : s.T) (o v0 : OneUnit p n (M*n)) (ho : o ∈ i.val) (hv0 : v0 ∈ j.val)
    (hcompat : oneMatchProg x n (o,v0)) (hsecure : oneSecureAt s (o,v0)) :
    ∃ f : PredictedFile p (onePreparationPins b),
      f.leftTest v (m n) x.α (fun i => x.g i n) ε η x.c i j o ∧
      f.rightTest v (m n) x.α (fun i => x.g i n) ε η x.c i j v0 := by
  classical
  have hK k : imagePlanRank (s.pin (Subtype.val (show s.T from k))).sp ≤ (onePreparationPins b) :=
    (h.strength.leaf _ k.property).bound
  obtain ⟨A,hA⟩ := sizedCharts v hv i (hK i)
  obtain ⟨B,hB⟩ := sizedCharts v hv j (hK j)
  let X := v.cAxes i (toRates A)
  let Z := v.cAxes j (toRates B)
  obtain ⟨⟨hmark,hclaim⟩,hglint,hexact⟩ := hmarks _ i.property o ho
  obtain ⟨⟨hmark',hclaim'⟩,hglint',hexact'⟩ := hmarks _ j.property v0 hv0
  have hroot : s.rooting o=(s.pin i.val).sp :=
    congrArg ImagePin.sp (ImageLeafMixture.poller_eq s h.strength.part i.property ho)
  have hroot' : s.rooting v0=(s.pin j.val).sp :=
    congrArg ImagePin.sp (ImageLeafMixture.poller_eq s h.strength.part j.property hv0)
  have hmem k : x.m n o k ∈ oneEffectivePins (oneEndpointPrimalPins (s.pin i.val).sp) k := hroot ▸ (hmark k).2
  have hmem' k : x.m n v0 k ∈ oneEffectivePins (oneEndpointPrimalPins (s.pin j.val).sp) k := hroot' ▸ (hmark' k).2
  choose a ha using fun k => show x.m n o k ∈ LinearMap.range (X k) from
    (hA k).1.symm ▸ hmem k
  choose b0 hb0 using fun k => show x.m n v0 k ∈ LinearMap.range (Z k) from
    (hB k).1.symm ▸ hmem' k
  let Y := onePredictorPartition x.c (fun i => x.g i n)
  let Γ : PredictionData p (toRates A) (toRates B) predictorCellCount :=
    ⟨x.α,predictorPulse x.c,a,b0⟩
  obtain ⟨k,hk⟩ := issueTicket v o v0 i j h.strength.part ho hv0 hv
    (h.strength.leaf _ i.property).closed (h.strength.leaf _ j.property).closed hsecure
  let T := v.mails i j k
  have hcomp : x.c.compatible x.α (glint p (x.m n o))
      (oneCardTone (x.m n) o T,oneCardTone (x.m n) v0 (fun e=>(T e)ᵀ)) := by
    have he1 l : oneCardTone (x.m n) o T l=
        (oneQuench (fun a=>oneMarkedDelta a (x.m n a)) (o,v0)).1 l :=
      (one_fits_tone _ _ (h.strength.leaf _ i.property).closed T _ (x.m n) o hk.2.2 hmem l).trans
        (one_actual_tone (x.m n) o v0 (fun k=>((one_effective_mem _ _ _).mp (hmem k)).1) l)
    have he2 l : oneCardTone (x.m n) v0 (fun e=>(T e)ᵀ) l=
        (oneQuench (fun a=>oneMarkedDelta a (x.m n a)) (o,v0)).2 l := by
      have hf := one_fits_table_reciprocal _ _ _ _ hk.2.2
      simp_rw [one_cross_reciprocal] at hf
      exact (one_fits_tone _ _ (h.strength.leaf _ j.property).closed _ _ (x.m n) v0 hf hmem' l).trans
        (one_actual_tone (x.m n) v0 o (fun k=>((one_effective_mem _ _ _).mp (hmem' k)).1) l)
    rw [funext he1,funext he2,hglint]
    exact hcompat
  have hlit : x.c.lit x.α := hclass ▸ one_finite_lit _ _
  have hsolve := one_attained_scalar_soluble (fun i=>x.g i n) x.α x.c hclass hrows a b0 η
    hcells (x.m n) o v0 T X Z ha hb0 hE.planted.hG (hglint.trans hglint'.symm) hcomp
  obtain ⟨P,hP⟩ := predicted_plan_exists Γ (oneWisp p Y) η (oneHailing X Z T)
    (fun _ => rfl) hE.planted.hG hsolve
  have hc : oneClaimed o (onePreparedPredictor x.c (fun i => x.g i n)) (m n)
      (fun k => X k (Γ.X k)) Γ.α (x.L n o) ε := by
    simpa only [Γ,ha] using prepared_claimed x.c x.α hlit _ (m n) (x.m n) o (x.L n o)
      hε hε' hclaim hexact
  have hc' : oneClaimed v0 (onePreparedPredictor x.c (fun i => x.g i n)) (m n)
      (fun k => Z k (Γ.Y k)) Γ.α (x.L n v0) ε := by
    simpa only [Γ,hb0] using prepared_claimed x.c x.α hlit _ (m n) (x.m n) v0 (x.L n v0)
      hε hε' hclaim' hexact'
  have hframe := h.cover _ i.property o ho
  have hframe' := h.cover _ j.property v0 hv0
  have hlabels : b.B+2^(oneSelectorProtectionDim p (onePreparationPins b)+12) <
      Fintype.card (Label p.b) := by
    have hpow : 2^(oneSelectorProtectionDim p (onePreparationPins b)+12) ≤
        oneScalarBudget p (onePreparationPins b) := by
      unfold oneScalarBudget
      gcongr <;> omega
    have hreserve := hE.reserve
    have hspare := hE.spare
    omega
  obtain ⟨qa,qb,hchance,hsteady,hsteady',hready,hready'⟩ := one_predicted_options_of_plan P Γ Y
    (onePreparedPredictor x.c (fun i => x.g i n)) (one_predictor_pulse_eq x.c _) η X Z T hP
    (s.pin i.val) (s.pin j.val) o v0 (m n)
    (by rw [hE.affine]) hE.jump hE.planted.hG hE.planted.hg hlabels hA hB (hK i) (hK j)
    (fun k => Nat.lt_succ_iff.mp (A k).isLt) (fun k => Nat.lt_succ_iff.mp (B k).isLt)
    hk.1 hk.2.1 hframe hframe' (x.L n o) (x.L n v0) (fun k => (hmark k).1)
    (fun k => (hmark' k).1) ε hc hc'
  let vol : Volumes := fun l => ⟨P.q l,by have hh := (hP.short l).2; omega⟩
  let f : PredictedFile p (onePreparationPins b) := ⟨⟨(vol,A,B),k,⟨P.tag,P.diag,qa,qb⟩⟩,P.cell⟩
  have hlarge : f.large Y η := hcal f Y hP.kept
  have hpin := (h.strength.leaf _ i.property).fixpin o ho
  have hpin' := (h.strength.leaf _ j.property).fixpin v0 hv0
  obtain ⟨hflag,hflag'⟩ := ticket_flags (s.pin i.val) (s.pin j.val) T o v0 hk hpin hpin'
  exact ⟨f,⟨hlarge,⟨hchance,hpin,hframe,hflag⟩,hsteady,hready⟩,
    ⟨hlarge,⟨hchance,hpin',hframe',hflag'⟩,hsteady',hready'⟩⟩

end OneOptions
end
end Lax793645Proofs.Simplifications
