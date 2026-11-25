/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.HistogramBounds.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RestrictedComparisonLaws
import Lax793645Proofs.Simplifications.UniformHitBounds
import Lax793645Proofs.Simplifications.QuadraticNets
import Lax793645Proofs.Simplifications.ColoredQuadratic

namespace Lax793645Proofs.Upstream.OAI

/-! # Histogram Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open Lax793645Proofs.Simplifications
open scoped BigOperators
variable {A X B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

def fromFlags (μ : Wgt A) (w : Wgt X) (v : A→X→Y) (K : A→X→B) :=
  fun z => ∃ P:A→ Y→ Prop,z=flaggedW μ w v K P

def Haberdash (Q : Wgt B→ Prop) (r : ℕ) (δ R η ε : ℝ) :=
  (∀ p,Q p→SubLaw p) ∧ roster Q r ε ∧ smallSet Q unif δ η ∧
  ∀ P : B→Prop,
    let v := unifOn P
    let H := hung Q P
    roster H r ε ∧ smallSet H v δ η ∧ rosterTail H v R η

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

namespace Template
set_option maxHeartbeats 1200000 in
theorem legacy_controls (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] [Nonempty Y]
    (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
    ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n; let A := UnitType p n N
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt A), IsLaw w →
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) →
      ∀ (f : A→Inputs p n I→Y),
        let Q := fromFlags w (prodW x) f (v.resultKey)
        Haberdash Q r δ R η ε := by
  classical
  obtain ⟨V,hV⟩ := hist_calendar v M hM C hC
  let U := V + log (num Y)
  obtain ⟨δ,hδ,_,hh⟩ := ui_threshold U η hη
  obtain ⟨r,a,ha,he⟩ := ample_thresh U (ε/2) (by positivity)
  obtain ⟨s,hR⟩ := roster_price r ε hε
  let D := min a δ; let z := max r 2
  refine ⟨s,δ,δ⁻¹,hδ,inv_pos_of_pos hδ,?_⟩
  filter_upwards [hV z D (Nat.cast_nonneg _) (lt_min ha hδ)]
    with n hn N A m hN w hw h x hx hz f Q
  let X := prodW x
  let K := resultKey v (n:=n) (N:=N)
  let B := Keys (p:=p) v.t N
  let μ := colored w X f
  let q := coloredP X f K
  have hX : IsLaw X := prodW_law hx
  have hu := colored_ultra hw hX K f
  have hg : tariffs μ q z D U := by
    intro C _ hC F hF
    refine (colored_budget K f F hX hw).trans ?_
    exact add_le_add_left (hn m hN w hw h x hx hz _ (by exact_mod_cast hC) F hF) _
  have h1 := tariffs_monotone hg (le_max_left ..) (min_le_left ..)
  have h2 := tariffs_monotone hg (le_max_right ..) (min_le_right ..)
  have ha := he (A×Y) B μ q hu h1
  have h3 (y : Wgt B) (hy : Q y) : catalog μ q y := by
    obtain ⟨P,rfl⟩ := hy
    exact flag_catalog K f P hX hw
  have h4 (y : Wgt B) (hy : Q y) : SubLaw y := hu.cat_sub _ (h3 y hy)
  have hi : roster Q s ε :=
    roster_mono Q _ h3 s ε (hR (A×Y) B μ q hu ha)
  have hj : smallSet Q unif δ η := fun i ht S hS =>
      (pr_mono_left (hu.cat_dom i (h3 i ht)).2 S).trans (hh (A×Y) B μ q hu h2 S hS)
  exact ⟨h4,hi,hj,fun P => ⟨hung_roster Q P _ _ hi,hung_small Q P _ _ hj,hung_tail Q P h4
    _ _ hδ hj⟩⟩
set_option maxHeartbeats 1200000 in
theorem controls (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] [Nonempty Y]
    (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
    ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n; let A := UnitType p n N
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt A), IsLaw w →
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) →
      ∀ (f : A→Inputs p n I→Y),
        let Q := fromFlags w (prodW x) f (v.resultKey)
        Haberdash Q r δ R η ε := by
  classical
  obtain ⟨B,a,hB,ha,ha',hcal⟩ := uniform_hit_calendar v M hM C hC
  have hB0 : 0<B := by linarith
  let U := num Y*B+1
  let α := ε/(32*B)
  have hα : 0<α := by positivity
  obtain ⟨r,β,hβ,hample⟩ := quadratic_ample_thresh U (ε/2) α (by positivity) hα
  obtain ⟨s,hR⟩ := roster_price r ε hε
  let δ := η/(2*B)
  have hδ : 0<δ := by positivity
  have hv : Tendsto (fun n : ℕ => bp (-a*n)) atTop (nhds 0) :=
    (bp_tendsto_zero ha).comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ => bp (-10*n)) atTop (nhds 0) :=
    (bp_tendsto_zero (by norm_num : (0:ℝ)<10)).comp tendsto_natCast_atTop_atTop
  have hτ : Tendsto (fun n : ℕ => 2*B*bp (-a*n)+bp (-10*n)) atTop (nhds 0) := by
    simpa using (hv.const_mul (2*B)).add he
  have hE : Tendsto (fun n : ℕ => (r:ℝ)*bp (-10*n)/β) atTop (nhds 0) := by
    simpa using (he.const_mul (r:ℝ)).div_const β
  refine ⟨s,δ,δ⁻¹,hδ,inv_pos_of_pos hδ,?_⟩
  filter_upwards [hcal, hv.eventually (eventually_le_nhds hβ),
    hv.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4)),
    hτ.eventually (eventually_le_nhds (lt_min (by positivity : 0<η/2) (by positivity : 0<ε/32))),
    hE.eventually (eventually_le_nhds zero_lt_one)]
    with n hn hnβ hnq hnτ hnE N A m hN w hw h x hx hz f Q
  let X := prodW x
  let K := resultKey v (n:=n) (N:=N)
  let T := Keys (p:=p) v.t N
  let μ := colored w X f
  let q := coloredP X f K
  have hX : IsLaw X := prodW_law hx
  have hu := colored_ultra hw hX K f
  have htail := hn m hN w hw h x hx hz
  have hset := query_setwise_from_tails v w hw x hx B (bp (-a*n)) (bp (-10*n)) hB0.le
    (bp_pos _) (by linarith) (bp_pos _).le htail
  have hmix : mixW μ q=mixW w (fun o => v.heatMap o x) := colored_mixture w X hX K f
  have hsmall : ∀ S : T→Prop, pr unif S≤α → pr (mixW μ q) S≤(ε/2)/8 := by
    intro S hS
    rw [hmix]
    have h := hset S
    have hh := mul_le_mul_of_nonneg_left hS hB0.le
    have he : B*α=ε/32 := by unfold α; field_simp
    rw [he] at hh
    linarith only [h,hh,(le_min_iff.mp hnτ).2]
  have hg : quadraticTariffs μ q r β U := by
    intro D _ hD F hF
    have ht (c : D) : pr w (fun o => B*mapW unif F c < mapW (mapW X (K o)) F c)≤bp (-10*n) := by
      by_cases hc : mapW (unif : Wgt T) F c=0
      · have hf (o : A) : mapW (mapW X (K o)) F c=0 := by
          by_contra ho
          have hs : lsupp (mapW X (K o)) (unif : Wgt T) := fun t _ => by
            rw [unif_apply]; positivity
          exact (lsupp.map hs unif_law.nz F c ho) hc
        simp only [hc,hf,mul_zero,lt_self_iff_false,pr_false]
        exact (bp_pos _).le
      · exact htail (fun t => F t=c) (hnβ.trans (hF c hc))
    have h0 := colored_quadratic_bound w X hw hX K f F B β (bp (-10*n)) hB0.le hβ hF ht
    have h1 : num D*bp (-10*n)/β ≤ 1 :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hD)
        (bp_pos _).le) hβ.le).trans hnE
    exact h0.trans (by unfold U; linarith)
  have ha := hample (A×Y) T μ q hu hsmall hg
  have h3 (y : Wgt T) (hy : Q y) : catalog μ q y := by
    obtain ⟨P,rfl⟩ := hy
    exact flag_catalog K f P hX hw
  have h4 (y : Wgt T) (hy : Q y) : SubLaw y := hu.cat_sub _ (h3 y hy)
  have hi : roster Q s ε := roster_mono Q _ h3 s ε (hR (A×Y) T μ q hu ha)
  have hj : smallSet Q unif δ η := by
    intro y hy S hS
    have h0 := pr_mono_left (hu.cat_dom y (h3 y hy)).2 S
    rw [hmix] at h0
    have h1 := hset S
    have h2 := mul_le_mul_of_nonneg_left hS hB0.le
    have he : B*δ=η/2 := by unfold δ; field_simp
    rw [he] at h2
    linarith only [h0,h1,h2,(le_min_iff.mp hnτ).1]
  exact ⟨h4,hi,hj,fun P => ⟨hung_roster Q P _ _ hi,hung_small Q P _ _ hj,
    hung_tail Q P h4 _ _ hδ hj⟩⟩

end Template
end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
