/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.KeyProjectionBounds.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UniformLeafComparisons
import Lax793645Proofs.Simplifications.SuccessfulFiniteProjection
import Lax793645Proofs.Simplifications.ProjectedDensityMend

namespace Lax793645Proofs.Upstream.OAI

/-! # Key Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap
open scoped BigOperators Topology
variable {p:Shape} {n N M K r s0 : ℕ}
namespace StatusAnalysis
open Station
namespace Station
variable {q:Format} {d e:Rates} {w : LeafMixture p n N} (t : Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (μ:Wgt (UnitType p n N)) (k:Fin (2^deckMax p K))
    (Y:Silhouette p N r)

variable {B : Type} [Fintype B]
def taxLeft (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageLeft t x m μ k Y i j a) P)
      (mapW (t.leftSales x m μ i j k) P)
def taxRight (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageRight t x m μ k Y i j a) P)
      (mapW (t.rightSales x m μ i j k) P)
def due (P : Keys (p:=p) x.t N→B) :=
    avg (pairW (portionW μ w.T) (portionW μ w.T)) (fun i=>
       taxLeft t x m μ k Y P i.1 i.2+taxRight t x m μ k Y P i.1 i.2)
def dueEnough {l:ℕ} (ε η:ℝ) (P : Keys (p:=p) x.t N→ Fin l) :=
    ∀ r:ℕ,∀ Y:Silhouette p N r, due t x m μ k Y P ≤ η → stratum t x m μ k Y ≤ ε
end Station

open PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {s : rhythms p M} {w:tale p M}

set_option maxHeartbeats 1800000 in
theorem projectCut {q:Format} {d e:Rates} (x:Typus p q d e)
    (h:x.permission)
    (k:Fin (2^deckMax p b.pins))
    (hv:veil p M b s0 l m s w) (t:Stations p M b.pins s)
    (ε:ℝ) (he:0<ε) :
    ∃ (r:ℕ) (η:ℝ), 0<η∧∀ᶠ n in l, let N:=M*n;
      ∃ P:Keys (p:=p) x.t N→Fin r,
      dueEnough (t n) x (m n) (w n) k ε η P := by
  classical
  let H := (ε/2)^2/8
  have hH : 0<H:=by unfold H; positivity
  have hE:=hv.easel
  have ht:=hE.enter.first
  obtain ⟨r,hcal⟩:=Lax793645Proofs.Simplifications.successful_finite_projection
    x.qA x.qB x.t x.z h.2.1 h.2.2.1 ht.hR M ht.hM b.leafNew H hH
  obtain ⟨u,hu,hd'⟩:=veil.score_cost hv t
  refine ⟨r,H,hH,?_⟩
  have hl:=hv.timeL
  have hz:=(trend_sizes l hl ht.hM).2
  let L:=2*netFact (trayPort p x.t)
  have hg : ∀ᶠ n in l,L*bp (-((M*n:ℕ):ℝ)/2)≤ε/2 := by
    have hvary:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have hh:=hvary.eventually (eventually_le_nhds (by rw [mul_zero]; exact half_pos he))
    filter_upwards [hh] with n hn
    change L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ))≤ε/2 at hn
    rwa [show -(1/2:ℝ)*((M*n:ℕ):ℝ)= -((M*n:ℕ):ℝ)/2 from by ring] at hn
  filter_upwards [hv.upright,hv.moment,hv.durableS.mass.positive,hv.durableS.shape,
    hcal.filter_mono hl,hd',(hu.lim hz).eventually (eventually_le_nhds hH),hg,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hn ht' hm he' hx hh h' hR hN N
  let v:=t n
  let w':=w n
  let s':=s n
  let I:=s'.T
  let F (i:↑I):=partW w' i.val
  let u:=portionW w' I
  let ν:=lawNu p N x.t x.z
  have ht0 : IsLaw w':=ht'.1.law
  have hF i (hi:i∈I) : IsLaw (partW w' i):=on_law ht0.nz (he'.1.leaf i hi).pos
  have hX i (hi:i∈I):=(he'.1.leaf i hi).density
  have hu : IsLaw u:=(rebuild ht0.nz he'.1.part (fun i hi=>(he'.1.leaf i hi).pos) hm).1
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change _≤(N:ℝ) at hN
    linarith only [hN]
  have hν : IsLaw ν:=nuLaw x.t x.z hhN
  obtain ⟨P,hP⟩:=hx (m n) hn.cols (↑I) u hu F (fun i=>hF _ i.property)
    (fun i=>hX _ i.property) (fun i=>v.cAxes i d) (fun i=>v.cAxes i e)
  refine ⟨P,fun z Y hs=>?_⟩
  let W:=pairW u u
  have hW:=pairW_law hu hu
  let A (i:↑I×↑I):=v.leftSales x (m n) w' i.1 i.2 k
  let B (i:↑I×↑I):=v.rightSales x (m n) w' i.1 i.2 k
  let C (i:↑I×↑I):=dip ν (banner ν P (density ν (A i))) (banner ν P (density ν (B i)))
  let D (i:↑I×↑I):=taxLeft v x (m n) w' k Y P i.1 i.2+taxRight v x (m n) w' k Y P i.1 i.2
  let g (i:↑I×↑I):=stagePlane v x (m n) w' k Y i.1 i.2
  let f (i:↑I×↑I):=Station.eclipse v x (m n) w' k Y i.1 i.2
  have hA1 i : IsLaw (x.qA.policies x.t x.z n i):=
    Appearance.witLaw (x.qA.allure_apt _ _ h.2.1 _) ht.hR hn.age
  have hB1 i : IsLaw (x.qB.policies x.t x.z n i):=
    Appearance.witLaw (x.qB.allure_apt _ _ h.2.2.1 _) ht.hR hn.age
  have hproj : avg W C≤v.arena x (m n) w' k+H :=
    hP (fun i=>v.frontPage x (m n) i.1 i.2 k) (fun i=>v.backPage x (m n) i.1 i.2 k)
  have hpoint i : g i^2≤C i+D i := by
    apply Lax793645Proofs.Simplifications.projected_density_mend ν hν P
      (stageLeft v x (m n) w' k Y i.1 i.2) (stageRight v x (m n) w' k Y i.1 i.2) (A i) (B i)
      (x.qA.bower_case _ _ _ _ _ _ _ (hF _ i.1.property) hA1)
      (x.qB.bower_case _ _ _ _ _ _ _ (hF _ i.2.property) hB1)
      (x.qA.sales_pos _ _ _ _ _ _ (hF _ i.1.property).nz)
      (x.qB.sales_pos _ _ _ _ _ _ (hF _ i.2.property).nz)
    · intro y hy
      apply Lax793645Proofs.Simplifications.uniform_on_support (ownPart x.t x.z) y
      by_contra ho
      exact hy (x.qA.sales_part _ _ _ _ _ _ y ho)
    · intro y hy
      apply Lax793645Proofs.Simplifications.uniform_on_support (ownPart x.t x.z) y
      by_contra ho
      exact hy (x.qB.sales_part _ _ _ _ _ _ y ho)
  apply skylineMean W f g (fun i=>C i+D i) ε he.le hW _ hpoint
    (fun i=>(eclipse_beam v x (m n) w' k Y i.1 i.2 hF hA1 hB1 hhN).trans hR)
  have hc : v.arena x (m n) w' k≤H:=((le_abs_self _).trans (hh q d e x k)).trans h'
  have hd : avg W D≤H:=hs
  rw [avg_add]
  rw [show (ε/2)^2=8*H from by unfold H; ring]
  linarith only [hproj,hc,hd,hH]

end StatusAnalysis
end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
