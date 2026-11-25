import Lax793645Proofs.Simplifications.OnePredictedMassBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneStation StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
namespace OneOptions
variable {p : Shape} {M s0 : ℕ} {b : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}

theorem slight_positive_part {x : ℕ → ℝ} (h : slight l x) :
    Tendsto (fun n => max (x n) 0) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact .of_forall fun n => ha.trans_le (le_max_right _ _)
  · intro a ha
    filter_upwards [h (a/2) (half_pos ha)] with n hn
    exact max_lt (hn.trans_lt (by linarith only [ha])) ha

set_option maxHeartbeats 1500000 in
theorem predicted_asymptotic_bounds (v : OneStations p M (onePreparationPins b) s)
    (h : OneVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank)
    (x : OneSketch p M) (hx : OneBright b l m s x) (hlinear : oneLinearLedger b x l) {β : ℝ} (hβ : 0 < β) :
    ∃ z : ℕ → ℝ,
      (∀ k : ℕ, Tendsto (fun n => z n*((2*(M*n):ℕ):ℝ)^k) l (𝓝 0)) ∧
      ∀ᶠ n in l,
        oneGilded s w x n ≤ 2*β*Fintype.card (PredictedFile p (onePreparationPins b))+z n ∧
        (∀ γ : ℝ,oneCompatibilityFloor (s n) (w n) (oneMatchProg x n) γ →
          2*β*Fintype.card (PredictedFile p (onePreparationPins b)) ≤ γ/2 →
          oneGlow s w x n ≤ 2*oneGleam s w x n+z n) := by
  classical
  let R:=exactPredictorRows p b
  let η := bp (-((2*R:ℕ):ℝ))/2
  have hη : 0<η := half_pos (bp_pos _)
  have hη1 : η≤1 := by
    have hle : bp (-((2*R:ℕ):ℝ))≤1 :=
      (bp_le (neg_nonpos.mpr (Nat.cast_nonneg (2*R)))).trans_eq bp_zero
    dsimp only [η]
    linarith
  let ε n := max (x.ε n) 0
  let a (f : PredictedFile p (onePreparationPins b)) n :=
    f.mass (v n) (m n) x.α (fun i => x.g i n) (ε n) η x.c (w n) β
  let z n := ∑ f : PredictedFile p (onePreparationPins b), a f n
  have ha f : ExpSmall l (fun n => (n:ℝ)) (a f) :=
    predicted_file_small v h f hβ hη hη1 x.c x.α (fun n i => x.g i n) ε
      (slight_positive_part hx.forecasts.small)
  refine ⟨z,?_,?_⟩
  · intro k
    have hz : Tendsto (fun n : ℕ => (n:ℝ)) l atTop :=
      tendsto_natCast_atTop_atTop.mono_left h.time
    have hf f : Tendsto (fun n => a f n*((2*(M*n):ℕ):ℝ)^k) l (𝓝 0) := by
      have hh := (((ha f).poly hz k).lim hz).mul_const ((2*(M:ℝ))^k)
      rw [zero_mul] at hh
      exact hh.congr fun n => by push_cast; ring
    have hh := tendsto_finsetSum univ (fun f _ => hf f)
    simpa only [sum_const_zero,←Finset.sum_mul] using hh
  · filter_upwards [h.durable.shape,h.moment,h.durable.mass.positive,hv,hx.engraved,hlinear,
      (one_predictor_cell_calendar p M R h.parameters.unary.hM).filter_mono h.time,
      (trend_sizes l h.time h.parameters.unary.hM).2.eventually
        (eventually_ge_atTop (2*num (Toast p)+1)),
      predicted_file_calendar (K:=(onePreparationPins b)) h.time h.parameters.unary.hM hη]
      with n hs hm hmass hv hmarks hlinear hcells hN hcal
    have hlead : OneLead (w n) (s n) (m n) b.leafNew (2*b.ζ) (onePreparationPins b) := ⟨hs.1,hmass,hm.1.law,hs.2⟩
    exact predicted_mass_bounds x (s n) (v n) m (w n) hv hlead h.parameters hmarks
      hlinear.2 hlinear.1 (hcells x.c (fun i=>x.g i n) hlinear.1)
      (le_max_right _ _) (le_max_left _ _) hβ (by linarith only [hN]) hcal

theorem predicted_gold_end (v : OneStations p M (onePreparationPins b) s)
    (h : OneVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank) (hl : l.NeBot)
    (x : OneSketch p M) (hx : OneBright b l m s x) (hlinear : oneLinearLedger b x l)
    (hout : oneGlowOutcome l w s x) : False := by
  classical
  obtain ⟨δ,hδ,hout⟩ := hout
  let C : ℝ := Fintype.card (PredictedFile p (onePreparationPins b))
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let β := δ/(4*(C+1))
  have hβ : 0 < β := by unfold β; positivity
  have hsize : 2*β*C ≤ δ/2 := by
    unfold β
    have hd : 0 < 4*(C+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith only [hδ,hC]
  obtain ⟨z,hz,hbound⟩ := predicted_asymptotic_bounds v h hv x hx hlinear hβ
  have hzero : Tendsto z l (𝓝 0) := by simpa using hz 0
  have hf : ∀ᶠ n in l, False := by
    filter_upwards [hout,hbound,hzero.eventually (gt_mem_nhds (half_pos hδ))] with n ho hb hz
    have hh := hb.1
    change _ ≤ 2*β*C+z n at hh
    linarith only [ho,hh,hsize,hz]
  exact hf.exists.elim fun _ h => h

theorem predicted_dim_end (v : OneStations p M (onePreparationPins b) s)
    (h : OneVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank) (hl : l.NeBot)
    (x : OneSketch p M) (hx : OneBright b l m s x) (hlinear : oneLinearLedger b x l)
    (hout : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in l,
      oneCompatibilityFloor (s n) (w n) (oneMatchProg x n) δ ∧ δ/((2*(M*n):ℕ):ℝ)^4 ≤ oneGlow s w x n ∧
        oneGleam s w x n ≤ 0.001*oneGlow s w x n) : False := by
  classical
  obtain ⟨δ,hδ,hout⟩ := hout
  let C : ℝ := Fintype.card (PredictedFile p (onePreparationPins b))
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let β := δ/(4*(C+1))
  have hβ : 0 < β := by unfold β; positivity
  have hsize : 2*β*C ≤ δ/2 := by
    unfold β
    have hd : 0 < 4*(C+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith only [hC,hδ]
  obtain ⟨z,hz,hbound⟩ := predicted_asymptotic_bounds v h hv x hx hlinear hβ
  have hf : ∀ᶠ n in l, False := by
    filter_upwards [hout,hbound,(hz 4).eventually (gt_mem_nhds (half_pos hδ)),
      (trend_sizes l h.time h.parameters.unary.hM).2.eventually (eventually_gt_atTop 0)]
      with n ho hb hz hN
    have hh := hb.2 δ ho.1 hsize
    have hp : 0 < ((2*(M*n):ℕ):ℝ)^4 := by
      rw [Nat.cast_mul,Nat.cast_ofNat]
      exact pow_pos (mul_pos (by norm_num) hN) _
    have he := (lt_div_iff₀ hp).mpr hz
    rw [show δ/2/((2*(M*n):ℕ):ℝ)^4 = (δ/((2*(M*n):ℕ):ℝ)^4)/2 from by ring] at he
    linarith only [ho.2.1,ho.2.2,hh,he,div_pos hδ hp]
  exact hf.exists.elim fun _ h => h

end OneOptions
end
end Lax793645Proofs.Simplifications
