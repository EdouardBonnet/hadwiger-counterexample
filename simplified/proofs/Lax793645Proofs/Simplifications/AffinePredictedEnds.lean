import Lax793645Proofs.Simplifications.AffinePredictedMassBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Station StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p : Shape} {M s0 : ℕ} {b : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : rhythms p M} {w : tale p M}

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
theorem predicted_asymptotic_bounds (v : Stations p M b.pins s)
    (h : AffineVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank)
    (x : Sketch p M) (hx : b.bright l p M m s x) {β : ℝ} (hβ : 0 < β) :
    ∃ z : ℕ → ℝ,
      (∀ k : ℕ, Tendsto (fun n => z n*((M*n:ℕ):ℝ)^k) l (𝓝 0)) ∧
      ∀ᶠ n in l,
        gilded s w x n ≤ 2*β*Fintype.card (PredictedFile p b.pins)+z n ∧
        (b.hardened p (M*n) (s n) (x.m n) →
          2*β*Fintype.card (PredictedFile p b.pins) ≤ 1/2 →
          glow s w x n ≤ 2*gleam s w x n+z n) := by
  classical
  obtain ⟨τ,hτ,hrec⟩ := hx.forecasts.classes
  let τ' := min τ (1/4)
  let η := τ'/8
  have hτ' : 0 < τ' := lt_min hτ (by norm_num)
  have hη : 0 < η := by unfold η; positivity
  have hη1 : η ≤ 1 := by
    have ht : τ' ≤ 1/4 := min_le_right _ _
    unfold η; linarith only [ht]
  let ε n := max (x.ε n) 0
  let a (f : PredictedFile p b.pins) n :=
    f.mass (v n) (m n) x.α (fun i => x.g i n) (ε n) η x.c (w n) β
  let z n := ∑ f : PredictedFile p b.pins, a f n
  have ha f : ExpSmall l (fun n => (n:ℝ)) (a f) :=
    predicted_file_small v h f hβ hη hη1 x.c x.α (fun n i => x.g i n) ε
      (slight_positive_part hx.forecasts.small)
  refine ⟨z,?_,?_⟩
  · intro k
    have hz : Tendsto (fun n : ℕ => (n:ℝ)) l atTop :=
      tendsto_natCast_atTop_atTop.mono_left h.timeL
    have hf f : Tendsto (fun n => a f n*((M*n:ℕ):ℝ)^k) l (𝓝 0) := by
      have hh := (((ha f).poly hz k).lim hz).mul_const ((M:ℝ)^k)
      rw [zero_mul] at hh
      exact hh.congr fun n => by push_cast; ring
    have hh := tendsto_finsetSum univ (fun f _ => hf f)
    simpa only [sum_const_zero,←Finset.sum_mul] using hh
  · filter_upwards [h.durableS.shape,h.moment,h.durableS.mass.positive,hv,hx.engraved,hrec,
      (trend_sizes l h.timeL h.easel.enter.first.hM).2.eventually
        (eventually_ge_atTop (2*num (Toast p)+1)),
      predicted_file_calendar (K:=b.pins) h.timeL h.easel.enter.first.hM hη]
      with n hs hm hmass hv hmarks hrec hN hcal
    have hlead : Lead (w n) (s n) (m n) b := ⟨hs.1,hmass,hm.1.law,hs.2⟩
    have hrec' : x.c.recital p (fun i => x.g i n) x.α τ' :=
      ⟨hrec.1,fun i j a b c hi hg => hrec.2 i j a b c hi
        (fun l q => (hg l q).trans (min_le_left _ _))⟩
    exact predicted_mass_bounds x (s n) (v n) m (w n) hv hlead h.easel hmarks hrec'
      hη.le (by rw [predictorCellCount_eq]; unfold η; linarith)
      (by have hh : τ' ≤ 1/4 := min_le_right _ _; linarith only [hh])
      (le_max_right _ _) (le_max_left _ _) hβ (by linarith only [hN]) hcal

theorem predicted_gold_end (v : Stations p M b.pins s)
    (h : AffineVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank) (hl : l.NeBot)
    (x : Sketch p M) (hx : b.bright l p M m s x)
    (hout : glowOutcome l p M w s x) : False := by
  classical
  obtain ⟨δ,hδ,hout⟩ := hout
  let C : ℝ := Fintype.card (PredictedFile p b.pins)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let β := δ/(4*(C+1))
  have hβ : 0 < β := by unfold β; positivity
  have hsize : 2*β*C ≤ δ/2 := by
    unfold β
    have hd : 0 < 4*(C+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith only [hδ,hC]
  obtain ⟨z,hz,hbound⟩ := predicted_asymptotic_bounds v h hv x hx hβ
  have hzero : Tendsto z l (𝓝 0) := by simpa using hz 0
  have hf : ∀ᶠ n in l, False := by
    filter_upwards [hout,hbound,hzero.eventually (gt_mem_nhds (half_pos hδ))] with n ho hb hz
    have hh := hb.1
    change _ ≤ 2*β*C+z n at hh
    linarith only [ho,hh,hsize,hz]
  exact hf.exists.elim fun _ h => h

theorem predicted_dim_end (v : Stations p M b.pins s)
    (h : AffineVeil p M b s0 l m s w) (hv : ∀ᶠ n in l, (v n).bank) (hl : l.NeBot)
    (x : Sketch p M) (hx : b.bright l p M m s x)
    (hout : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in l,
      b.hardened p (M*n) (s n) (x.m n) ∧ δ/((M*n:ℕ):ℝ)^4 ≤ glow s w x n ∧
        gleam s w x n ≤ 0.001*glow s w x n) : False := by
  classical
  obtain ⟨δ,hδ,hout⟩ := hout
  let C : ℝ := Fintype.card (PredictedFile p b.pins)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let β := 1/(4*(C+1))
  have hβ : 0 < β := by unfold β; positivity
  have hsize : 2*β*C ≤ 1/2 := by
    unfold β
    have hd : 0 < 4*(C+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    field_simp
    nlinarith only [hC]
  obtain ⟨z,hz,hbound⟩ := predicted_asymptotic_bounds v h hv x hx hβ
  have hf : ∀ᶠ n in l, False := by
    filter_upwards [hout,hbound,(hz 4).eventually (gt_mem_nhds (half_pos hδ)),
      (trend_sizes l h.timeL h.easel.enter.first.hM).2.eventually (eventually_gt_atTop 0)]
      with n ho hb hz hN
    have hh := hb.2 ho.1 hsize
    have hp : 0 < ((M*n:ℕ):ℝ)^4 := pow_pos hN _
    have he := (lt_div_iff₀ hp).mpr hz
    rw [show δ/2/((M*n:ℕ):ℝ)^4 = (δ/((M*n:ℕ):ℝ)^4)/2 from by ring] at he
    linarith only [ho.2.1,ho.2.2,hh,he,div_pos hδ hp]
  exact hf.exists.elim fun _ h => h

end AffineOptions
end
end Lax793645Proofs.Simplifications
