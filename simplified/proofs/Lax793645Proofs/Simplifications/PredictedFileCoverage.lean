import Lax793645Proofs.Simplifications.PredictedFiles

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Station StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Finset Matrix Function LinearMap
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N M s0 : ℕ} {b : PreparationParameters}

theorem prepared_claimed (c : PredictionClass) (α : Party) (hc : c.lit α)
    (g : Bool → Augur p N) (m : Mixer p n) (z : BMark p n N)
    (o : UnitType p n N) (L : Stalls p) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ ε) (hclaim : claimed p o g m (z o) α L δ)
    (hexact : c=dusk → exactInk p m z o) :
    claimed p o (preparedPredictor c g) m (z o) α L ε := by
  classical
  by_cases hd : c=dusk
  · have ha := dusk_lit α (hd ▸ hc)
    intro i a ha' l f
    have he (y : Knobs p.g n) :
        ¬mismatch p (preparedPredictor c g i) (yoke p m o i (z o i) (α i)) l a f (onSide o i) y := by
      intro hbad
      apply hbad
      rw [ha]
      exact (hexact hd i _ (mem_useAtom ..)).trans (by simp [preparedPredictor,hd])
    simp_rw [eq_false (he _),pr_false]
    exact hε
  · simpa only [preparedPredictor,if_neg hd] using
      (show claimed p o g m (z o) α L ε from fun i a ha l f => (hclaim i a ha l f).trans hδ)

set_option maxHeartbeats 1500000 in
theorem predicted_file_coverage (x : Sketch p M) (s : LeafMixture p n (M*n))
    (v : Station p n (M*n) b.pins s) (m : cycleM p) (U : Wgt (UnitType p n (M*n)))
    (hv : v.bank) (h : Lead U s (m n) b) (hE : AnalyticParameters p M b s0)
    (hmarks : s.within (fun o => b.seems p (m n) s o (fun i => x.g i n)
      (x.m n o) (x.L n o) x.α (x.ε n) ∧ glint p (x.m n o)=x.r ∧
      (x.c=dusk → exactInk p (m n) (x.m n) o)))
    {τ η ε : ℝ} (hrec : x.c.recital p (fun i => x.g i n) x.α τ)
    (hη : 0 ≤ η) (hτ : (predictorCellCount:ℝ)*η ≤ τ) (hsmall : 2*τ < 1)
    (hε : 0 ≤ ε) (hε' : x.ε n ≤ ε)
    (hN : 2*num (Toast p)-((M*n:ℕ):ℝ) ≤ -1)
    (hcal : ∀ f : PredictedFile p b.pins,
      ∀ Y : Silhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ wisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η)
    (i j : s.T) (o v0 : UnitType p n (M*n)) (ho : o ∈ i.val) (hv0 : v0 ∈ j.val)
    (hcompat : matchProg x n (o,v0)) (hsecure : secureAt p s.rooting (o,v0)) :
    ∃ f : PredictedFile p b.pins,
      f.leftTest v (m n) x.α (fun i => x.g i n) ε η x.c i j o ∧
      f.rightTest v (m n) x.α (fun i => x.g i n) ε η x.c i j v0 := by
  classical
  have hK k : planRank (s.pin (Subtype.val (show s.T from k))).sp ≤ b.pins :=
    (h.strength.leaf _ k.property).bound
  obtain ⟨A,hA⟩ := sizedCharts b.pins s v hv i (hK i)
  obtain ⟨B,hB⟩ := sizedCharts b.pins s v hv j (hK j)
  let X := v.cAxes i (toRates A)
  let Z := v.cAxes j (toRates B)
  obtain ⟨⟨hmark,hclaim⟩,hglint,hexact⟩ := hmarks _ i.property o ho
  obtain ⟨⟨hmark',hclaim'⟩,hglint',hexact'⟩ := hmarks _ j.property v0 hv0
  have hroot : s.rooting o=(s.pin i.val).sp :=
    congrArg Pin.sp (LeafMixture.poller_eq s h.strength.part i.property ho)
  have hroot' : s.rooting v0=(s.pin j.val).sp :=
    congrArg Pin.sp (LeafMixture.poller_eq s h.strength.part j.property hv0)
  have hmem k : x.m n o k ∈ effective (s.pin i.val).sp k := hroot ▸ (hmark k).2
  have hmem' k : x.m n v0 k ∈ effective (s.pin j.val).sp k := hroot' ▸ (hmark' k).2
  choose a ha using fun k => show x.m n o k ∈ LinearMap.range (X k) from
    (hA k).1.symm ▸ hmem k
  choose b0 hb0 using fun k => show x.m n v0 k ∈ LinearMap.range (Z k) from
    (hB k).1.symm ▸ hmem' k
  let Y := predictorPartition x.c (fun i => x.g i n)
  let Γ : PredictionData p (toRates A) (toRates B) predictorCellCount :=
    ⟨x.α,predictorPulse x.c,a,b0⟩
  obtain ⟨k,hk⟩ := issueTicket o v0 s v i j h.strength.part ho hv0 hv hsecure
  let T := v.mails i j k
  have hcomp : x.c.compatible x.α (glint p (x.m n o))
      (cardTone (x.m n) o T,cardTone (x.m n) v0 (reciprocal p T)) := by
    have he1 l : cardTone (x.m n) o T l=(quench p (delta (x.m n)) (o,v0)).1 l :=
      (fitsTone (x.m n) o hk.2.2 hmem l).trans (actualTone (x.m n) o v0 l)
    have he2 l : cardTone (x.m n) v0 (reciprocal p T) l=
        (quench p (delta (x.m n)) (o,v0)).2 l := by
      have hf := fits_recip hk.2.2
      rw [reciprocal_actual] at hf
      exact (fitsTone (x.m n) v0 hf hmem' l).trans (actualTone (x.m n) v0 o l)
    rw [funext he1,funext he2,hglint]
    exact hcompat
  have hsolve := retained_scalar_soluble Γ (wisp p Y) x.c τ η (x.m n) o v0 T X Z
    ha hb0 hE.enter.first.hG (predictor_chorus x.c (fun i => x.g i n) x.α τ hrec a b0)
    (fun l q => mapW_law (omegaLaw p l q hN) _) (hglint.trans hglint'.symm) hcomp hη hτ hsmall
  obtain ⟨P,hP⟩ := predicted_plan_exists Γ (wisp p Y) η (hailing p X Z T)
    (fun _ => rfl) hE.enter.first.hG hsolve
  have hc : claimed p o (preparedPredictor x.c (fun i => x.g i n)) (m n)
      (fun k => X k (Γ.X k)) Γ.α (x.L n o) ε := by
    simpa only [Γ,ha] using prepared_claimed x.c x.α hrec.1 _ (m n) (x.m n) o (x.L n o)
      hε hε' hclaim hexact
  have hc' : claimed p v0 (preparedPredictor x.c (fun i => x.g i n)) (m n)
      (fun k => Z k (Γ.Y k)) Γ.α (x.L n v0) ε := by
    simpa only [Γ,hb0] using prepared_claimed x.c x.α hrec.1 _ (m n) (x.m n) v0 (x.L n v0)
      hε hε' hclaim' hexact'
  have hframe := h.coverC _ i.property o ho
  have hframe' := h.coverC _ j.property v0 hv0
  obtain ⟨qa,qb,hchance,hsteady,hsteady',hready,hready'⟩ := predicted_options_of_plan P Γ Y
    (preparedPredictor x.c (fun i => x.g i n)) (predictor_pulse_eq x.c _) η X Z T hP
    (s.pin i.val) (s.pin j.val) o v0 (m n) hE hA hB (hK i) (hK j)
    (fun k => Nat.lt_succ_iff.mp (A k).isLt) (fun k => Nat.lt_succ_iff.mp (B k).isLt)
    hk.1 hk.2.1 hframe hframe' (x.L n o) (x.L n v0) (fun k => (hmark k).1)
    (fun k => (hmark' k).1) ε hc hc'
  let vol : Volumes := fun l => ⟨P.q l,by have hh := (hP.short l).2; omega⟩
  let f : PredictedFile p b.pins := ⟨⟨(vol,A,B),k,⟨P.tag,P.diag,qa,qb⟩⟩,P.cell⟩
  have hlarge : f.large Y η := hcal f Y hP.kept
  have hpin := (h.strength.leaf _ i.property).fixpin o ho
  have hpin' := (h.strength.leaf _ j.property).fixpin v0 hv0
  obtain ⟨hflag,hflag'⟩ := berth_flags (s.pin i.val) (s.pin j.val) T hk hpin hpin'
  exact ⟨f,⟨hlarge,⟨hchance,hpin,hframe,hflag⟩,hsteady,hready⟩,
    ⟨hlarge,⟨hchance,hpin',hframe',hflag'⟩,hsteady',hready'⟩⟩

end
end Lax793645Proofs.Simplifications
