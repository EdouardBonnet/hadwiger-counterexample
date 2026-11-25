import Lax793645Proofs.Simplifications.OneGenericPopulationScores
import Lax793645Proofs.Simplifications.OneAnalyticAsymptotics

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter Finset Function
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

/-- Common linear cells for every finite numerical option. Both leaf draws
remain independent; the actual acceptance flags may depend on the pair. -/
theorem one_generic_late_scores (v:OneStations p M (onePreparationPins q) s)
    (h:OneVeil p M q s0 l m s w) (ε η:ℝ) (he:0<ε) (hη:0<η) (L R:ℕ):
    ∃ r coords:ℕ,∃ δ:ℝ,0<δ ∧ (r+1:ℝ)*δ≤η ∧ ∀ᶠ n in l,
      ∀ Y:OneSilhouette p (M*n) L,OneFullLinearSilhouette Y R →
      ∃ X:OneSilhouette p (M*n) r,OneRefines X Y ∧ OneFullLinearSilhouette X coords ∧
        pr ((s n).sap (w n)) (fun i=>¬oneGenericGauze p δ δ X (m n) (onePreparationPins q) i)≤η ∧
        ∀ i:OneScrip p (onePreparationPins q),(oneGenericPermission i.2.2) →
          (v n).stratum i.2.2 (m n) (w n) i.2.1 X≤ε := by
  obtain ⟨r,coords,θ,σ,hθ,hσ,hcal⟩:=
    OneStation.generic_simultaneous_calendar h.parameters.unary q.leafNew ε he
  obtain ⟨cost,hcost,hbound⟩:=h.score_cost v
  let d:=r*L
  let δ:=min θ (η/(d+1:ℝ))
  have hd:0<δ:=lt_min hθ (div_pos hη (by positivity))
  have hb:=one_generic_gauze_calendar d M h.parameters.unary δ δ hd hd
  have hf:=one_lit_fire_calendar p q.spJoint M h.parameters.thickness
  have hcostlim:=hcost.lim (one_trend_sizes l h.time h.parameters.planted.hM).2
  have hsm:0<min (σ/2) η:=lt_min (half_pos hσ) hη
  have hgsmall:∀ᶠ n:ℕ in atTop,bp (-(1/100:ℝ)*n)≤min (σ/2) η:=
    (bp_nat_vanish (by norm_num : (0:ℝ)<1/100)).eventually (eventually_le_nhds hsm)
  have hfsmall:∀ᶠ n:ℕ in atTop,bp (-(n:ℝ)*n/40)≤σ/2:=by
    filter_upwards [eventually_ge_atTop 1,
      (bp_nat_vanish (by norm_num : (0:ℝ)<1/40)).eventually
        (eventually_le_nhds (half_pos hσ))] with n hn hh
    refine (bp_le ?_).trans hh
    have hn':(1:ℝ)≤n:=by exact_mod_cast hn
    nlinarith only [hn']
  refine ⟨d,coords+R,δ,hd,?_,?_⟩
  · have hh:δ≤η/(d+1:ℝ):=min_le_right ..
    exact (mul_comm _ _).le.trans ((le_div_iff₀ (by positivity)).mp hh)
  filter_upwards [hcal.filter_mono h.time,hb.filter_mono h.time,hf.filter_mono h.time,
    h.parameters.planted.unary_room.filter_mono h.time,h.moment,h.durable.shape,
    h.durable.mass.positive,h.query_caps,hbound,
    hcostlim.eventually (eventually_le_nhds hσ),hgsmall.filter_mono h.time,
    hfsmall.filter_mono h.time]
    with n hn hg hf hroom hm hs hmass hc hbound hsmall hgsmall hfsmall Y hY
  obtain ⟨X,hX,hF⟩:=hn (m n) hm.2.2.1 hroom (s n) (w n) (2*q.ζ)
    hs.1 hm.1.law hmass hs.2 (v n)
  let Z:=oneDuoY X Y
  have hG:=hg (m n) ((s n).sap (w n)) hc.1 hc.2.1 hroom hm.2.1 Z
  have hfire:pr ((s n).sap (w n)) (fun o=>¬oneLitFire o)≤σ/2:=
    (hf (m n) hroom _ (by simpa only [Nat.cast_mul] using hc.2.2)).trans hfsmall
  refine ⟨Z,(one_duo_refines X Y).2,one_full_linear_duo hX hY,
    hG.trans (hgsmall.trans (min_le_right ..)),fun i hi=>?_⟩
  exact hF i hi d (coords+R) Z (one_full_linear_duo hX hY) (one_duo_refines X Y).1 δ δ (min_le_left ..)
    (hG.trans (hgsmall.trans (min_le_left ..))) hfire i.2.1
    ((hbound _ _ _ _ _).trans hsmall)

structure OneGenericBeams {n N r K:ℕ} (m:Mixer p n) (Y:OneSilhouette p N r)
    (pop:OneLeafMixture p n N) (μ:Wgt (OneUnit p n N))
    (v:OneStation p n N K pop) (a ε δ τ:ℝ):Prop where
  soft:StatusAnalysis.DualAnalysis.origami p r (oneWisp p Y) δ
  rare:pr (pop.sap μ) (fun i=>¬oneGenericGauze p δ δ Y m K i)≤τ
  zone:pr (oneCirque pop μ) (fun x=>v.genericEligiblePair m x.1 x.2 Y a)≤τ
  haze:0<δ ∧ δ≤ε

/-- Finite replacement for the common-limit proposition, with a fixed
positive option threshold and a bounded common linear partition. -/
theorem one_generic_lightmap (v:OneStations p M (onePreparationPins q) s)
    (h:OneVeil p M q s0 l m s w) (a ε τ:ℝ) (ha:0<a) (he:0<ε) (hτ:0<τ)
    (L R:ℕ) (Y:∀ n,OneSilhouette p (M*n) L)
    (hY:∀ n,OneFullLinearSilhouette (Y n) R):
    ∃ r coords:ℕ,∃ δ:ℝ,∀ᶠ n in l,
      ∃ X:OneSilhouette p (M*n) r,OneRefines X (Y n) ∧ OneFullLinearSilhouette X coords ∧
        OneGenericBeams (m n) X (s n) (w n) (v n) a ε δ τ := by
  let B:=num (OneScrip p (onePreparationPins q))
  have hB:0≤B:=Nat.cast_nonneg _
  let η:=a*τ/(B+1)
  have hη:0<η:=by dsimp [η]; positivity
  let u:=min τ (min ε (1/4))
  have hu:0<u:=lt_min hτ (lt_min he (by norm_num))
  obtain ⟨r,coords,δ,hd,hV,hT⟩:=one_generic_late_scores v h η u hη hu L R
  refine ⟨r,coords,δ,?_⟩
  have hz:=(trend_sizes l h.time h.parameters.planted.hM).2
  filter_upwards [hT,h.moment,h.durable.shape,h.durable.mass.positive,
    (eventually_ge_atTop (2*p.r)).filter_mono h.time,
    hz.eventually (eventually_ge_atTop (2*num (Toast p)+1))]
    with n hn hm hs hmass hnR hN
  obtain ⟨X,hX,hlin,hrare,hscore⟩:=hn (Y n) (hY n)
  refine ⟨X,hX,hlin,?_,hrare.trans (min_le_left ..),?_,hd,?_⟩
  · have h0 i j:IsLaw (oneWisp p X i j):=mapW_law
      (one_omega_law i j (by linarith only [hN])) _
    refine ⟨h0,fun i j=>?_⟩
    let ν:=oneWisp p X i j
    have heq:pr ν (fun x=>¬δ≤ν x)=1-pr ν (fun x=>δ≤ν x):=by
      rw [pr_not,(h0 i j).total]
    simp_rw [not_le] at heq
    have hf:=haze_small ν δ hd.le
    have hi:u≤1/4:=(min_le_right ..).trans (min_le_right ..)
    nlinarith only [hf,heq,hV,hi,hd]
  · apply ((v n).generic_prognosis (w n) (m n) X hη.le ha h.parameters.planted.hR hnR
      ⟨hs.1,hmass,hm.1.law,hs.2⟩ hscore).trans
    change B*(η/a)≤τ
    have hh:η/a=τ/(B+1):=by dsimp [η]; field_simp
    rw [hh,mul_div_assoc',div_le_iff₀ (by linarith)]
    linarith only [hτ]
  · have hi:u≤ε:=(min_le_right ..).trans (min_le_left ..)
    nlinarith only [hi,hV,hd,Nat.cast_nonneg (α:=ℝ) r]

end
end Lax793645Proofs.Simplifications
