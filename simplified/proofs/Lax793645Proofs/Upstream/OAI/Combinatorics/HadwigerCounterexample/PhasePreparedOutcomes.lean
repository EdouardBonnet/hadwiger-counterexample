/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.PhasePreparedOutcomes.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PreparedPopulationTrimming
import Lax793645Proofs.Simplifications.RankCompatibility

namespace Lax793645Proofs.Upstream.OAI

/-! # Phase Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P Q : Campaign p M}

def satisfied (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) :=
  ∃ t : rhythms p M,q.durable l p M m w t ∧ (q.silenceOutcome l p M m w t ∨
    q.predOutcome l p M m w t)

/-- Preparation with the chosen predictor functions retained explicitly. -/
def finished (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (b : Sketch p M) :=
  ∃ t : rhythms p M,q.durable l p M m w t ∧ q.bright l p M m t b ∧
    (glowOutcome l p M w t b ∨ q.glimmer l p M w t b)

theorem finished_satisfied (h : finished q l p M m w b) :
    satisfied q l p M m w := by
  obtain ⟨t,ht,hb,hout⟩:=h
  exact ⟨t,ht,Or.inr ⟨b,hb,hout⟩⟩

theorem byTorch_fixed (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hc : ∀ᶠ n in l,0.05 ≤ charm s w P b n) :
    finished q l p M m w b := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= dropHarvest hl hq hw hx hb
  refine ⟨t,hT,h1,Or.inl (hT.kindles hl hq hw ?_)⟩
  filter_upwards [hF,hc,(he.lim (trend_sizes l hl hq.hM).2).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 0.01))]
    with n hn ht hv
  linarith only [hn,ht,hv]

theorem byTorch (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hc : ∀ᶠ n in l,0.05 ≤ charm s w P b n) :
    satisfied q l p M m w := by
  exact finished_satisfied (byTorch_fixed hl hq hw hx hb hc)

theorem byCandle (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) (hn : q.nebulous l s w P b)
    {δ : ℝ} (hδ : 0<δ) (hc : ∀ᶠ n in l, δ ≤ charm s w P b n) :
    satisfied q l p M m w := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= dropHarvest hl hq hw hx hb
  have hk : q.domed l t b := by
    filter_upwards [hideOn hn hb hx,h2] with n hn hz
    obtain ⟨T,hT,hE⟩:=hn
    refine ⟨T,hT,fun i hi x hx=>?_⟩
    obtain ⟨⟨j,hj,hx'⟩,hv⟩:= hz i hi x hx
    exact hE j hj x hx' hv
  refine ⟨t,hT,Or.inr ⟨b,h1,Or.inl (hT.domeGlow hl hq hw hk (half_pos hδ) ?_)⟩⟩
  filter_upwards [hF,hc,(he.lim (trend_sizes l hl hq.hM).2).eventually
    (gt_mem_nhds (half_pos hδ))]
    with n hn ht hv
  linarith only [hn,ht,hv]

theorem byGlitter_fixed (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) (hn : q.nebulous l s w P b)
    {δ : ℝ} (hδ : 0<δ)
    (hc : ∀ᶠ n in l, δ/((M*n:ℕ):ℝ)^4 ≤ charm s w P b n) :
    finished q l p M m w b := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= pressHarvest hl hq hw hx hb hn
  let z (n:ℕ):=((M*n:ℕ):ℝ)
  have hz := (trend_sizes l hl hq.hM).2
  have hi : ∀ᶠ n in l,e n * (z n)^4 <δ/2 :=
    ((he.poly hz 4).lim hz).eventually (gt_mem_nhds (half_pos hδ))
  refine ⟨t,hT,h1,Or.inr (hT.domeSpark hl hq hw h2 (half_pos hδ) ?_)⟩
  filter_upwards [hF,hc,hz.eventually (eventually_gt_atTop 0),hi] with n hn ht hv h'
  have hz : 0< z n := hv
  have he := (lt_div_iff₀ (show 0 < (z n)^4 from by positivity)).mpr h'
  change (δ/2)/(z n)^4 ≤ _
  change δ/(z n)^4 ≤ _ at ht
  rw [show (δ/2)/(z n)^4= (δ/(z n)^4)/2 from by ring] at he ⊢
  linarith only [hn,ht,he]

theorem byGlitter (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) (hn : q.nebulous l s w P b)
    {δ : ℝ} (hδ : 0<δ)
    (hc : ∀ᶠ n in l, δ/((M*n:ℕ):ℝ)^4 ≤ charm s w P b n) :
    satisfied q l p M m w := by
  exact finished_satisfied (byGlitter_fixed hl hq hw hx hb hn hδ hc)

theorem citable_interpose (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (h : warm l (fun i=>((M*i:ℕ):ℝ)) (fun i=> pr (potion s w P i) (Q i))) :
    let Y:= fun i x=> P i x∧Q i x
    q.citable l p M m w s b Y ∧
    ∀ᶠ n in l,potion s w Y n=onW (potion s w P n) (Q n) := by
  classical
  let Y : Campaign p M := fun i x=>P i x∧Q i x
  have hz : ∀ᶠ n in l, IsLaw ((s n).sap (w n)) := by
    filter_upwards [hw,hx] with n hn h
    exact LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) h.weight) hn.law
  have hm : citable q l p M m w s b Y := by
    refine ⟨(hb.mass.mul h).mono ?_,hb.forecast, hb.mark.mono fun i hi j hj x hx h =>hi j hj x hx h.1⟩
    filter_upwards [hz] with n hn
    exact (pr_of_on hn.nz (P n) (Q n)).symm.le
  refine ⟨hm,?_⟩
  filter_upwards [hz,hb.mass.positive,h.positive] with n hn ht he
  exact (on_both ((s n).sap (w n)) (P n) (Q n) hn.nz ht he).symm

set_option maxHeartbeats 1000000 in
theorem outByMix_fixed (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hm : ∀ᶠ n in l, tonalMix p (delta (b.m n)) (potion s w P n)) :
    finished q l p M m w b := by
  classical
  refine byTorch_fixed hl hq hw hx hb ?_
  filter_upwards [hm,hb.on_law hl hq hw hx] with n hn ht
  obtain ⟨v,hv⟩:= meet b.c b.α b.r
  apply (mix_pattern p _ _ ht hn v).le.trans
  refine pr_mono (pairW_law ht ht).nz (fun x h=>?_); unfold matchProg matchUp; rw [h]; exact hv

theorem outByMix (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hm : ∀ᶠ n in l, tonalMix p (delta (b.m n)) (potion s w P n)) :
    satisfied q l p M m w := by
  exact finished_satisfied (outByMix_fixed hl hq hw hx hb hm)

variable {U : Ultrafilter ℕ}
set_option maxHeartbeats 1400000 in
theorem outByCover_fixed (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable (U:Filter ℕ) p M m w s b P)
    (hm : ∀ᶠ n in U, tonalTiny p (delta (b.m n)) (potion s w P n) q.d) :
    finished q (U:Filter ℕ) p M m w b := by
  classical
  let l:Filter ℕ:=U
  let v:= potion s w P
  have hc : q.nebulous (U:Filter ℕ) s w P b:= hm.mono (fun i h=> by
    obtain ⟨T,h1,h2,h3⟩:= h; exact ⟨T,h1,h2⟩)
  have hv := hb.on_law hl hq hw hx
  cases he : b.c with
  | noon =>
    refine byTorch_fixed hl hq hw hx hb ?_
    filter_upwards [hv] with n hn
    change _≤pr (pairW (v n) (v n)) _
    unfold matchProg matchUp; rw [he]
    simp [compatible, (pairW_law hn hn).total, v]; norm_num
  | dawn i =>
    let z (n : ℕ):=((M*n:ℕ):ℝ); have hz := (trend_sizes (U:Filter ℕ) hl hq.hM).2
    have ht : ∀ᶠ n in U,bp (-0.24*z n)<0.1 :=
      (((bp_tendsto_zero (by norm_num)).comp hz).eventually (gt_mem_nhds (by norm_num)))
    refine byTorch_fixed hl hq hw hx hb ?_
    filter_upwards [hv,ht,hm] with n hn ht hk
    unfold charm matchProg; rw [he]
    exact le_trans (by norm_num) (tiny_morn p _ _ hn q.d hk ht _ _ _)
  | twinned =>
    let C : ℝ := 2*q.d+2
    have hC : 0 < C := by unfold C; positivity
    refine byGlitter_fixed hl hq hw hx hb hc (δ:=1/C^2) (by positivity) ?_
    filter_upwards [hv,hm,(trend_sizes (U:Filter ℕ) hl hq.hM).2.eventually
      (eventually_ge_atTop 1)] with n hn ht hN
    obtain ⟨T,hT,hcover,_⟩ := ht
    have hrank := Lax793645Proofs.Simplifications.twinned_rank_compatibility T q.d hT b.α b.r
      (delta (b.m n)) (v n) hn hcover
    have hsquare : (2*(q.d:ℝ)*((M*n:ℕ):ℝ)+2)^2 ≤ C^2*((M*n:ℕ):ℝ)^4 := by
      calc
        _ ≤ (C*((M*n:ℕ):ℝ))^2 := by
          apply pow_le_pow_left₀ (by positivity)
          unfold C
          nlinarith only [hN]
        _ = C^2*((M*n:ℕ):ℝ)^2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hN (by decide : 2 ≤ 4)) (sq_nonneg C)
    unfold charm matchProg
    rw [he]
    apply le_trans _ hrank
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) hsquare
  | dusk =>
    obtain ⟨δ,hδ,hH⟩:= eventually_tiny_poll q.d
    refine byGlitter_fixed hl hq hw hx hb hc hδ ?_
    filter_upwards [hx,hv,hm,hb.mark,(trend_sizes (U:Filter ℕ) hl hq.hM).1.eventually hH]
      with n hn ht hv h hH
    apply hH.trans
    unfold charm matchProg matchUp; rw [he]
    refine tiny_poll p _ _ ht hv ?_ b.r
    intro x hx
    obtain ⟨hp,hx⟩:= onW_ne hx
    obtain ⟨⟨i,hi,hx⟩,_⟩:= LeafMixture.present hx
    obtain ⟨⟨hE,h1⟩,h2,h3⟩:= h i hi x hx hp
    exact diag_dusk (m n) (b.m n) x (fun i=> (effective_mem.mp (hE i).2).1) (h3 he)
      (hn.onTile i hi x hx).2.2.2

theorem outByCover (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable (U:Filter ℕ) p M m w s b P)
    (hm : ∀ᶠ n in U, tonalTiny p (delta (b.m n)) (potion s w P n) q.d) :
    satisfied q (U:Filter ℕ) p M m w := by
  exact finished_satisfied (outByCover_fixed hl hq hw hx hb hm)

end PreparationParameters
end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
