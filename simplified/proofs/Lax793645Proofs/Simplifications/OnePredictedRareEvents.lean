import Lax793645Proofs.Simplifications.OnePredictedQueryError
import Lax793645Proofs.Simplifications.OneBaseProductHits
import Lax793645Proofs.Simplifications.OneQueryMassBounds
import Lax793645Proofs.Simplifications.RestrictedSuperlevels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N:ℕ}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)

def oneNaturalSales (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (m:Mixer p n) (s:Charts p n d):Wgt (OneKeys t N):=
  mapW (oneSales w t z μ P m s) (oneQueryCoordinateEquiv t N)

theorem one_natural_sales_mean (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (m:Mixer p n) (s:Charts p n d) (f:Wgt (OneKeys t N)):
    avg (oneNaturalSales w t z μ P m s) f=
      avg μ (fun o=>ind (P o)*oneProwl w t z o m s f) := by
  unfold oneNaturalSales
  rw [mapW_avg]
  exact (finite_average_instances _ _ _ _).trans (one_sales_prowl w t z m s μ P f)

def OnePredictionReady (s:Charts p n d) (m:Mixer p n)
    (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E:OneKeys t N→Prop) (o:OneUnit p n N):Prop:=
  ∃ (coords:∀ j:Bool,Cell (d j)) (L:Bool→Finset (Label p.b)),
    oneClaimed o g m (fun j=>s j (coords j)) α L ε ∧
    (∀ i,w.sel i∉L (parcel b i)) ∧ OnePredictsOn w t z s coords α g E

def OnePredictedQualified (s:Charts p n d) (m:Mixer p n) (K:ℕ)
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop) (a:ℝ)
    (α:Party) (g:Bool→OneAugur p N) (ε:ℝ) (E:OneKeys t N→Prop):Prop:=
  2*a≤pr μ P ∧ ∀ o,P o → μ o≠0 →
    OneBaseSteady w m K s o ∧ OnePredictionReady w t z s m α g ε E o

set_option maxHeartbeats 1000000 in
theorem one_predicted_qualify_hit (s:Charts p n d) (m:Mixer p n) (K:ℕ)
    (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E H:OneKeys t N→Prop) (hHE:∀ x,H x → E x)
    {a h:ℝ} (hh:0<h)
    (hq:OnePredictedQualified w t z s m K μ P a α g ε E)
    (hμ:IsLaw μ) (hw:w.moral t z) (hr:1≤p.r) (hn:2*p.r≤n)
    (herr:Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε)≤h)
    (hbad:pr μ (fun o=>¬OneBaseSober w t z K H m (2*h) o)≤a):
    a*h≤pr (oneNaturalSales w t z μ P m s) H := by
  let Q:=OneBaseSober w t z K H m (2*h)
  let V o:=oneProwl w t z o m s (fun x=>ind (H x))
  have he:a≤pr μ (fun x=>P x ∧ Q x):=
    le_trans (by linarith only [hbad,hq.1]) (pr_shield hμ.nz P Q)
  unfold pr
  rw [one_natural_sales_mean w t z μ P m s (fun x=>ind (H x))]
  refine (mul_le_mul_of_nonneg_right he hh.le).trans ?_
  unfold pr
  rw [←avg_mul]
  unfold avg
  refine Finset.sum_le_sum fun o _=>?_
  dsimp only
  by_cases ho:μ o=0
  · simp only [ho,zero_mul]; rfl
  apply mul_le_mul_of_nonneg_left _ (hμ.nz o)
  have hstate:IsLaw ((w.pen t).state z n):=by
    change IsLaw (prodW (w.policies t z n))
    exact prodW_law fun i=>Appearance.witLaw (w.allure_apt t z hw i) hr hn
  have hV:0≤V o:=avg_nonneg hstate.nz fun x=>mul_nonneg (ind_nonneg _) (ind_nonneg _)
  by_cases hp:P o ∧ Q o
  · change ind (_∧_)*_≤_*V o
    rw [ind_one hp,ind_one hp.1,one_mul,one_mul]
    obtain ⟨hb,coords,L,hclaim,hfresh,hcell⟩:=hq.2 o hp.1 ho
    have hbase:=hp.2 s hb
    have hfull:=one_predicted_query_error w t z s m o coords α g L hclaim hfresh hw hr hn H
      (fun k hk=>hcell k (hHE k hk))
    change _≤V o at hfull
    linarith only [hbase,hfull,herr]
  rw [ind_zero hp,zero_mul]
  exact mul_nonneg (ind_nonneg _) hV

theorem one_natural_sales_nonneg (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (m:Mixer p n) (s:Charts p n d) (hμ:∀ o,0≤μ o):
    ∀ x,0≤oneNaturalSales w t z μ P m s x := by
  rw [oneNaturalSales,one_sales_histogram]
  intro x
  apply avg_nonneg (prodW_nonneg fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _))
  exact fun _=>pr_nonneg hμ

theorem one_natural_sales_mono_filter (s:Charts p n d) (m:Mixer p n)
    (μ:Wgt (OneUnit p n N)) (P Q:OneUnit p n N→Prop)
    (hμ:∀ o,0≤μ o) (hPQ:∀ o,P o → Q o):
    ∀ x,oneNaturalSales w t z μ P m s x≤oneNaturalSales w t z μ Q m s x := by
  simp only [oneNaturalSales,one_sales_histogram]
  intro x
  apply avg_mono (prodW_nonneg fun _=>normW_nonneg (subW_nonneg (spins_law ..).nz _))
  exact fun _=>pr_mono hμ (fun o ho=>⟨⟨hPQ o ho.1.1,ho.1.2⟩,ho.2⟩)

end OneQuill

namespace OneStation
variable {p:Shape} {q:Format} {d e:Rates} {n N K:ℕ} {pop:OneLeafMixture p n N}
    (v:OneStation p n N K pop) (x:Typus p q d e)
    (m:Mixer p n) (k:Fin (2^oneDeckMax p K)) (μ:Wgt (OneUnit p n N))

def predictedCharter (a:ℝ) (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E:OneKeys x.t N→Prop) (i:pop.T×pop.T):Prop:=
  (onePermission x) ∧ ∃ P Q:OneUnit p n N→Prop,
    (∀ o,P o → v.frontPage x m i.1 i.2 k o) ∧
    (∀ o,Q o → v.backPage x m i.1 i.2 k o) ∧
    OneQuill.OnePredictedQualified x.qA x.t x.z (v.cAxes i.1 d) m K
      (partW μ i.1.val) P a α g ε E ∧
    OneQuill.OnePredictedQualified x.qB x.t x.z (v.cAxes i.2 e) m K
      (partW μ i.2.val) Q a α g ε E

def predictedBerth (a:ℝ) (α:Party) (g:Bool→OneAugur p N) (ε:ℝ)
    (E:OneKeys x.t N→Prop):ℝ:=
  pr (pairW (portionW μ pop.T) (portionW μ pop.T))
    (v.predictedCharter x m k μ a α g ε E)

end OneStation
end
end Lax793645Proofs.Simplifications
