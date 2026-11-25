/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.SimultaneousProjection.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Simplifications.AffineAdaptiveProjection
import Lax793645Proofs.Simplifications.LinearPaintComparisons

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample

/-! # Simultaneous Projection -/

noncomputable section
open Filter Finset Matrix
open scoped BigOperators Topology
open StatusAnalysis
namespace AffineOptions
open Station PreparationParameters

variable {p : Shape} {M s0 n N K : ℕ} {q:Format} {d e:Rates}
    {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {w:tale p M} {s:rhythms p M}

def sparks (v : Stations p M b.pins s) (i:Scrip p b.pins) (m:cycleM p) (w:tale p M)
    {r} (n:ℕ) (Y: Silhouette p (M*n) r) :=
  AffineOptions.stratum (v n) i.2.2 (m n) (w n) i.2.1 Y

def bullseye (v: Stations p M K s) (m:cycleM p) (w:tale p M) (x:Typus p q d e)
    (k : Fin (2^deckMax p K)) (ε : ℝ) {r : ℕ} (n : ℕ) (Y : Silhouette p (M*n) r)
    (τ u:ℝ) :=
  ∀ (r':ℕ) (Y':Silhouette p (M*n) r'),refines Y' Y →
  ∀ τ' δ:ℝ,τ'≤τ →
    pr ((s n).sap (w n)) (fun i=>¬ gauze p τ' δ Y' (m n) K i) ≤u →
    AffineOptions.stratum (v n) x (m n) (w n) k Y'≤ ε

set_option maxHeartbeats 2400000 in
theorem glowLamp (v:Stations p M b.pins s) (h:AffineVeil p M b s0 l m s w) (x:Typus p q d e)
    (k:Fin (2^deckMax p b.pins)) (hP:x.permission) (ε:ℝ) (he:0<ε) :
    ∃ (r coords : ℕ) (τ u:ℝ), 0<τ∧0<u∧∀ᶠ n in l,∃ Y:Silhouette p (M*n) r,
      LinearSilhouette Y coords ∧ bullseye v m w x k ε n Y τ u := by
  classical
  have hq:=h.easel; have ht:=hq.enter.first
  obtain ⟨z,paints,rows,η,hη,hX⟩:=projectCut x hP k h v ε he
  let a:= η/(12*(z+1:ℝ))
  have ha:0<a:=by unfold a; positivity
  obtain ⟨u,hi,hA⟩:=linear_paint_side_release x.qA x.t x.z M hq.toQueryParameters hP.2.1 rows a ha
  obtain ⟨v',hj,hB⟩:=linear_paint_side_release x.qB x.t x.z M hq.toQueryParameters hP.2.2.1 rows a ha
  let i:=linearPaletteSize (Messenger q) rows
  let coord:=linearPaletteRank (Messenger q) rows
  let j:=i
  let f:=fun _ : Fin z=>i*j; let r:=bouquet f
  let τ:= min u v'
  refine ⟨r,(∑ _ : Fin z,(coord+coord)),τ,a,lt_min hi hj,ha,?_⟩
  have hz:= (trend_sizes l h.timeL ht.hM).2
  filter_upwards [hX,h.upright,h.durableS.shape,h.durableS.mass.positive,h.moment,
    hA.filter_mono h.timeL,hB.filter_mono h.timeL,
    ((bp_nat_vanish (by norm_num : (0:ℝ)<1/100)).eventually (eventually_le_nhds ha)).filter_mono h.timeL,
    ((bp_nat_vanish (by norm_num : (0:ℝ)<1/100)).eventually (eventually_le_nhds ha)).filter_mono h.timeL,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hn ha' hB' hW he' hA hB hM hV hG
  let N:=M*n; let p0:=s n
  obtain ⟨P,hPlinear,_,hP'⟩:=hn
  let e k y:=ind (P y=k)
  have heq k y : |e k y| ≤1 := by unfold e; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hcell k : HasLinearCells (fun (_ : F) y=>e k y) rows :=
    linear_cells_postprocess hPlinear (fun (_ : F) j=>ind (j=k))
  choose X hXL hF using fun i:Fin z=> hA (e i) (heq i) (hcell i)
  choose Z hZL hF' using fun i:Fin z=> hB (e i) (heq i) (hcell i)
  let Y k:=duoY (X k) (Z k)
  refine ⟨bundleY f Y,linear_silhouette_bundle f Y (fun _=>coord+coord)
    (fun k=>linear_silhouette_duo (hXL k) (hZL k)),fun r Y' hR τ' δ hτ hpos=>?_⟩
  apply hP' r Y'
  have hw:=he'.1.law
  let hh:=hB'.1
  have hx' i : IsLaw (x.qA.policies x.t x.z n i) :=
    Appearance.witLaw (x.qA.allure_apt _ _ hP.2.1 _) ht.hR ha'.age
  have hy' i : IsLaw (x.qB.policies x.t x.z n i) :=
    Appearance.witLaw (x.qB.allure_apt _ _ hP.2.2.1 _) ht.hR ha'.age
  have hN:= show 2*num (Messenger q×Toast p)-(N:ℝ) ≤ -1 from by
    change _ ≤ (N:ℝ) at hG; linarith only [hG]
  have hp := nuLaw x.t x.z hN
  have ht' : ∀ i:Fin z,refines Y' (Y i) := fun i=> refines_next hR (bundle_refines f Y i)
  refine (projectSum (v n) x (m n) k (w n) Y' P hh.part hw (fun i hi=>(hh.leaf i hi).pos)
    hW hx' hy' hp a u v' τ' a δ ha.le hP ⟨hτ.trans (min_le_left ..),hτ.trans (min_le_right ..)⟩
    hpos (fun i=>?_) (fun i=>?_)).trans ?_
  · exact (hF i _ Y' (refines_next (ht' i) (duo_good ..).1) _ _ ha').trans hM
  · exact (hF' i _ Y' (refines_next (ht' i) (duo_good ..).2) _ _ ha').trans hV
  have hi : 12*(z+1:ℝ)*a=η := by unfold a; field_simp
  nlinarith only [hi,ha,(Nat.cast_nonneg z : 0≤(z:ℝ))]

private theorem minimums {A:Type} [Fintype A] (x : Wgt A) (hx:∀ i,0<x i) :
    ∃ ε : ℝ,0<ε ∧ ∀ i, ε ≤ x i := by
  classical
  cases isEmpty_or_nonempty A
  next he => exact ⟨1,zero_lt_one,fun i=> (he.false i).elim⟩
  next he =>
    let f:= univ.image x
    have hf : f.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    obtain ⟨i,hi,ht⟩:= mem_image.mp (Finset.min'_mem _ hf)
    exact ⟨f.min' hf,ht ▸ hx i,fun i=>Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ i))⟩

set_option maxHeartbeats 1400000 in
theorem twinkle (v:Stations p M b.pins s) (h:AffineVeil p M b s0 l m s w)
    (ε:ℝ) (he:0<ε) :
    ∃ (r coords : ℕ) (τ u:ℝ),0<τ∧0<u∧∀ᶠ n in l,∃ Y:Silhouette p (M*n) r,
      LinearSilhouette Y coords ∧
        ∀ i:Scrip p b.pins, i.2.2.permission → bullseye v m w i.2.2 i.2.1 ε n Y τ u := by
  classical
  choose r coords q A hr hq hh using
    (fun i:Scrip p b.pins=> show ∃ (r coords : ℕ) (τ u:ℝ),0<τ∧0<u∧∀ᶠ n in l,
      ∃ Y:Silhouette p (M*n) r,LinearSilhouette Y coords ∧
        (i.2.2.permission → bullseye v m w i.2.2 i.2.1 ε n Y τ u) from by
       by_cases hP : i.2.2.permission
       · obtain ⟨r,coords,τ,u,hτ,hu,hh⟩:=glowLamp v h i.2.2 i.2.1 hP ε he
         refine ⟨r,coords,τ,u,hτ,hu,hh.mono (fun i hi=> ?_)⟩
         obtain ⟨Y,hYlin,hY⟩:=hi; exact ⟨Y,hYlin,fun _=>hY⟩
       exact ⟨1,0,1,1,zero_lt_one,zero_lt_one,.of_forall (fun n=>
         ⟨fun _ _ _=>0,linear_silhouette_constant (fun _ _=>0),fun hi=>(hP hi).elim⟩)⟩)
  obtain ⟨δ,hd,hd'⟩:=minimums q hr
  obtain ⟨e,he,he'⟩:=minimums A hq
  refine ⟨bouquet r,∑ i,coords i,δ,e,hd,he,?_⟩
  filter_upwards [eventually_all.mpr hh] with n hn
  choose F hFlin hF using hn
  refine ⟨bundleY r F,linear_silhouette_bundle r F coords hFlin,
    fun i hi r' Y' hR τ' δ' hτ hp=> ?_⟩
  exact hF i hi r' Y' (refines_next hR (bundle_refines r F i)) _ _ (hτ.trans (hd' _)) (hp.trans (he' _))

set_option maxHeartbeats 1200000 in
theorem lateSilk (v:Stations p M b.pins s) (h:AffineVeil p M b s0 l m s w)
    (ε η:ℝ) (he:0<ε) (hη:0<η) (L:ℕ) :
    ∃ (r coords:ℕ) (δ:ℝ),0<δ ∧ (r+1:ℝ)*δ≤η ∧ ∀ᶠ n in l,
    ∀ Y:Silhouette p (M*n) L,∃ X:Silhouette p (M*n) r, refines X Y ∧
      (∀ R,LinearSilhouette Y R → LinearSilhouette X (coords+R)) ∧
      pr ((s n).sap (w n)) (fun i=>¬ gauze p δ δ X (m n) b.pins i)≤ η ∧
      ∀ i:Scrip p b.pins,i.2.2.permission →
         sparks (b:=b) v i m w n X ≤ ε := by
  classical
  obtain ⟨r,coords,τ,u,hτ,hu,hg⟩:= twinkle v h ε he
  let d:=r*L
  let a:= d+1; let δ := min τ (η/(a:ℝ))
  have hD : 0<(a:ℝ):=by unfold a; positivity
  have hd : 0<δ:=lt_min hτ (by positivity)
  have hb := gauzeCalendar p d M h.easel.toQueryParameters δ δ hd hd
  refine ⟨d,coords,δ,hd,?_,?_⟩
  · have hh := (le_div_iff₀ hD).mp (show δ ≤ η/(a:ℝ) from min_le_right ..)
    rw [mul_comm]; simpa [a] using hh
  filter_upwards [hg,hb.filter_mono h.timeL,h.upright,((bp_nat_vanish (by norm_num :
    (0:ℝ)<1/100)).eventually (eventually_le_nhds (lt_min hu hη))).filter_mono h.timeL]
    with n hn hb hc hz Y
  obtain ⟨X,hXlin,hX⟩:=hn
  let Z:= duoY X Y
  have hm := (hb _ _ hc Z).trans hz
  exact ⟨Z,(duo_good X Y).2,fun R hYlin=>linear_silhouette_duo hXlin hYlin,
    hm.trans (min_le_right ..),fun i h=> hX i h d Z (duo_good X Y).1
    δ δ (min_le_left ..) (hm.trans (min_le_left ..))⟩
end AffineOptions

end

end Lax793645Proofs.Simplifications
