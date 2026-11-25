/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.KeyProjectionBounds.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UniformLeafComparisons
import Lax793645Proofs.Simplifications.AffineLeafSurrogates
import Lax793645Proofs.Simplifications.AffineAsymptotics
import Lax793645Proofs.Simplifications.AffinePredictedHits
import Lax793645Proofs.Simplifications.ClippedProductProjection
import Lax793645Proofs.Simplifications.LightQueryBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample

/-! # Key Projection Bounds -/

noncomputable section
open Filter Finset Matrix LinearMap
open scoped BigOperators Topology
variable {p:Shape} {n N M K r s0 : ℕ}
open StatusAnalysis
namespace AffineOptions
variable {q:Format} {d e:Rates} {w : LeafMixture p n N} (t : Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (μ:Wgt (UnitType p n N)) (k:Fin (2^deckMax p K))
    (Y:Silhouette p N r)

variable {B : Type} [Fintype B]
def taxLeft (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageLeft t x m μ k Y i j a) P)
      (mapW (rawLeftSales t x m μ k i j) P)
def taxRight (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageRight t x m μ k Y i j a) P)
      (mapW (rawRightSales t x m μ k i j) P)
def due (P : Keys (p:=p) x.t N→B) :=
    avg (pairW (portionW μ w.T) (portionW μ w.T)) (fun i=>
       taxLeft t x m μ k Y P i.1 i.2+taxRight t x m μ k Y P i.1 i.2)
def dueEnough {l:ℕ} (ε η:ℝ) (P : Keys (p:=p) x.t N→ Fin l) :=
    ∀ r:ℕ,∀ Y:Silhouette p N r, due t x m μ k Y P ≤ η → stratum t x m μ k Y ≤ ε

open PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {s : rhythms p M} {w:tale p M}

set_option maxHeartbeats 1800000 in
theorem projectCut {q:Format} {d e:Rates} (x:Typus p q d e)
    (h:x.permission)
    (k:Fin (2^deckMax p b.pins))
    (hv:AffineVeil p M b s0 l m s w) (t:Stations p M b.pins s)
    (ε:ℝ) (he:0<ε) :
    ∃ (r paints rows:ℕ) (η:ℝ), 0<η∧∀ᶠ n in l, let N:=M*n;
      ∃ P:Keys (p:=p) x.t N→Fin r,
      HasLinearCells (fun (_ : F) y=>P y) rows ∧
      (∀ i : Fin r,Template.design (x.qA.pen x.t) (fun y=>ind (P y=i)) 1 paints ∧
        Template.design (x.qB.pen x.t) (fun y=>ind (P y=i)) 1 paints) ∧
      dueEnough (t n) x (m n) (w n) k ε η P := by
  classical
  let H := (ε/2)^2/8
  have hH : 0<H:=by unfold H; positivity
  have hE:=hv.easel
  have ht:=hE.enter.first
  obtain ⟨_,Ra,_,ha,hA⟩:=ordinary_light_certificate x.qA x.t x.z M ht.hM ht.hR
    b.leafNew (by unfold leafNew leafOld; positivity) h.2.1 H hH
  obtain ⟨_,Rb,_,hβ,hB⟩:=ordinary_light_certificate x.qB x.t x.z M ht.hM ht.hR
    b.leafNew (by unfold leafNew leafOld; positivity) h.2.2.1 H hH
  let R:= max Ra Rb
  have hr :0<R:=lt_max_of_lt_left ha
  obtain ⟨r,paints,rows,hlinear⟩:=clipped_successful_product_projection x.qA x.qB x.t x.z
    h.2.1 h.2.2.1 ht.hR M ht.hM b.leafNew R H hr hH
  obtain ⟨u,hu,hd'⟩:=AffineVeil.score_cost hv t
  refine ⟨r,paints,rows,H,hH,?_⟩
  have hl:= hv.timeL
  have hz:=(trend_sizes l hl ht.hM).2
  let L:= 2*netFact (trayPort p x.t)
  have hg : ∀ᶠ n in l, L*bp (-((M*n:ℕ):ℝ)/2)≤ ε/2 := by
    have hx:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have heq : ∀ᶠ n in l,L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ))≤ ε/2 :=
      hx.eventually (eventually_le_nhds (by rw [mul_zero]; linarith only [he]))
    filter_upwards [heq] with n hn; rw [show -((M*n:ℕ):ℝ)/2= -(1/2:ℝ)*((M*n:ℕ):ℝ) from by ring]; exact hn
  let rejection (n : ℕ) := bp (num (Messenger q)+(baseProtectionDim p b.pins : ℝ)-(n : ℝ))
  have hrejection : ∀ᶠ n in l, R*(rejection n+rejection n) ≤ H := by
    have hlim := (affine_rejection_vanish p b.pins (Fintype.card (Messenger q))).mono_left hl
    simpa only [mul_zero,add_zero] using
      ((hlim.add hlim).const_mul R).eventually
        (eventually_le_nhds (by simpa only [add_zero,mul_zero] using hH))
  filter_upwards [hlinear.filter_mono hl,hrejection,hv.upright,hv.moment, hv.durableS.mass.positive,hv.durableS.shape,hA.filter_mono hl,
    hB.filter_mono hl,hd',(hu.lim hz).eventually (eventually_le_nhds hH),hg,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hlinear hrejection hn ht' hm he' hx hy hh h' hR hN N
  let v:= t n
  let w':=w n; let s':= s n
  let I := s'.T
  let F (i : ↑I):= partW w' i.val
  let A (i : ↑I) := x.qA.custom (F i) (v.cAxes i d) x.t x.z (m n)
  let B (i : ↑I) := x.qB.custom (F i) (v.cAxes i e) x.t x.z (m n)
  let u:=portionW w' I; let ν:=lawNu p N x.t x.z
  have ht0 : IsLaw w':=ht'.1.law
  have hF i (hi : i∈I): IsLaw (partW w' i):= on_law ht0.nz
    (he'.1.leaf i hi).pos
  have hX i (hi : i∈I) := (he'.1.leaf _ hi).density
  have hA' (i:↑I) :
      (∀ f,A i f → SubLaw f ∧ lsupp f ν) ∧ rosterTail (A i) ν R H := by
    have hh:=hx (m n) (v.cAxes i d) (F i) hn.cols (hF _ i.property) (hX _ i.property)
    refine ⟨hh.1,fun f hf=>?_⟩
    exact (pr_mono (hh.1 f hf).1.nz
      (fun k hk=>(le_max_left Ra Rb).trans hk)).trans (hh.2.2 f hf)
  have hB' (i:↑I) :
      (∀ f,B i f → SubLaw f ∧ lsupp f ν) ∧ rosterTail (B i) ν R H := by
    have hh:=hy (m n) (v.cAxes i e) (F i) hn.cols (hF _ i.property) (hX _ i.property)
    refine ⟨hh.1,fun f hf=>?_⟩
    exact (pr_mono (hh.1 f hf).1.nz
      (fun k hk=>(le_max_right Ra Rb).trans hk)).trans (hh.2.2 f hf)
  have hu :IsLaw u := (rebuild ht0.nz he'.1.part (fun i hi=>(he'.1.leaf _ hi).pos) hm).1
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change _≤(N:ℝ) at hN; linarith only [hN]
  have hν : IsLaw ν := nuLaw x.t x.z hhN
  obtain ⟨Q,hQlinear,hpaints,hP⟩:=hlinear (m n) hn.cols (↑I) u hu F
    (fun i=>hF _ i.property) (fun i=>hX _ i.property)
    (fun i=>v.cAxes i d) (fun i=>v.cAxes i e)
  refine ⟨Q,hQlinear,hpaints,fun z Y hs=>?_⟩
  let W := pairW u u
  have hW:=pairW_law hu hu
  let L := fun x':↑I×↑I => rawLeftSales (t n) x (m n) (w n) k x'.1 x'.2
  let U' := fun x':↑I×↑I => rawRightSales (t n) x (m n) (w n) k x'.1 x'.2

  have hχ (i:↑I×↑I) : A i.1 (L i) := x.qA.sales_custom _ _ _ _ _ _
  have hν' (i:↑I×↑I) : B i.2 (U' i) := x.qB.sales_custom _ _ _ _ _ _
  let J(i:↑I×↑I):=|rebate ν (mcut R ν (L i)) (mcut R ν (U' i)) Q|
  have he1 :
      avg W J≤H := by
    exact hP (fun i=>frontPage v x (m n) i.1 i.2 k)
      (fun i=>backPage v x (m n) i.1 i.2 k)
  let g := fun i : ↑I×↑I=> stagePlane v x (m n) (w n) k Y i.1 i.2
  let f := fun i : ↑I×↑I=> AffineOptions.eclipse v x (m n) (w n) k Y i.1 i.2
  let C := fun i : ↑I×↑I=> matchScore v x (m n) (w n) i.1 i.2 k
  let D := fun i:↑I×↑I=> taxLeft v x (m n) (w n) k Y Q i.1 i.2+taxRight v x
    (m n) (w n) k Y Q i.1 i.2
  have hA1 i : IsLaw (x.qA.policies x.t x.z n i) :=
    Appearance.witLaw (x.qA.allure_apt _ _ h.2.1 _) ht.hR hn.age
  have hB1 i : IsLaw (x.qB.policies x.t x.z n i) :=
    Appearance.witLaw (x.qB.allure_apt _ _ h.2.2.1 _) ht.hR hn.age
  let X i:= C i+J i+D i+(3*H)
  have hP : ∀ i,g i^2≤ X i := by
    intro i
    let A' := stageLeft v x (m n) (w n) k Y i.1 i.2
    let B' := stageRight v x (m n) (w n) k Y i.1 i.2
    have hh := hχ i; have hk:= hν' i
    obtain ⟨h1,h2⟩:= (hA' _).1 _ hh
    obtain ⟨h3,h4⟩:= (hB' _).1 _ hk
    have hrejectA := affine_sales_rejection_of_filter x.qA x.t x.z (s'.pin i.1.val) b.pins
      (F i.1) (frontPage v x (m n) i.1 i.2 k) (m n) (v.cAxes i.1 d)
      (hF _ i.1.property).sub h.2.1 ht.hR hn.age (fun o ho => ho.1.2.1.2.1)
    have hrejectB := affine_sales_rejection_of_filter x.qB x.t x.z (s'.pin i.2.val) b.pins
      (F i.2) (backPage v x (m n) i.1 i.2 k) (m n) (v.cAxes i.2 e)
      (hF _ i.2.property).sub h.2.2.1 ht.hR hn.age (fun o ho => ho.1.2.2.2.1)
    have h := density_mend_after_rejection ν hν Q R hr.le A' B' (L i) (U' i)
      (leftSales v x (m n) (w n) i.1 i.2 k) (rightSales v x (m n) (w n) i.1 i.2 k) (x.qA.bower_case _ _ _ _ _ _ _ (hF _ i.1.property)
      hA1) (x.qB.bower_case _ _ _ _ _ _ _ (hF _ i.2.property) hB1) h1 h3 h2 h4
      hrejectA.1 hrejectB.1 (rejection n) (rejection n) hrejectA.2 hrejectB.2
    have he1 : trayLoss R ν (L i) ≤ H := (hA' _).2 _ hh
    have he2 : trayLoss R ν (U' i)≤ H := (hB' _).2 _ hk
    let a:=taxLeft v x (m n) (w n) k Y Q i.1 i.2
    let b0:=taxRight v x (m n) (w n) k Y Q i.1 i.2
    change g i^2 ≤ C i+ J i+(a+trayLoss R ν (L i)+(b0+trayLoss R ν (U' i)))+R*(rejection n+rejection n) at h
    change _ ≤ C i+J i+(a+b0)+3*H
    linarith only [he1,he2,h,hrejection]
  refine skylineMean W f g X ε he.le hW ?_ hP (fun i=> (eclipse_beam v x (m n) (w n)
    k Y i.1 i.2 hF hA1 hB1 hhN).trans hR)
  have hc : avg W C≤ H := le_trans ((le_abs_self _).trans (hh q d e x k)) h'
  unfold X; rw [avg_add,avg_add,avg_add]
  have hj : avg W (fun _=> 3*H)=3*H := hW.avg_const _
  rw [hj]
  change avg W D≤ H at hs
  rw [show (ε/2)^2=8*H from by unfold H; ring]; linarith only [hc,he1,hs,hH]
end AffineOptions

end

end Lax793645Proofs.Simplifications
