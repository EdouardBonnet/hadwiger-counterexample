import Lax793645Proofs.Simplifications.OneOptionContracts
import Lax793645Proofs.Simplifications.OnePreparationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K : ℕ}

abbrev OneScrip (p : Shape) (K : ℕ):=Σ q : Master K,Fin (2^oneDeckMax p K)×OnFile p q

instance oneScripFintype (p : Shape) (K : ℕ) : Fintype (OneScrip p K):=by
  classical
  infer_instance

structure OneStation (p : Shape) (n N K : ℕ) (s : OneLeafMixture p n N) where
  cAxes : s.T→(d : Rates)→Charts p n d
  mails : s.T→s.T→Fin (2^oneDeckMax p K)→OneCross p n

namespace OneStation
variable {s : OneLeafMixture p n N} (v : OneStation p n N K s)

def bank :=
  (∀ i,let d:=fun j=>dim (oneEffectivePins (oneEndpointPrimalPins (s.pin i.val).sp) j)
    oneCharted (v.cAxes i d) (s.pin i.val).sp) ∧
  ∀ i j T,∃ k,oneFitsTable (s.pin i.val).sp (s.pin j.val).sp (v.mails i j k) T

theorem create (h : ∀ i:s.T,imagePlanRank (s.pin i.val).sp≤K) :
    ∃ v : OneStation p n N K s,v.bank := by
  let d (i:s.T) j:=dim (oneEffectivePins (oneEndpointPrimalPins (s.pin i.val).sp) j)
  choose F hF using fun i:s.T=>one_chart_create (s.pin i.val).sp
  choose G hG using fun i j:s.T=>one_deck_cast (s.pin i.val).sp (s.pin j.val).sp K
    (fun e=>(image_plan_component_dimension _ e).trans (h i))
    (fun e=>(image_plan_component_dimension _ e).trans (h j))
  let axes (i:s.T) (r:Rates):Charts p n r:=if ht:r=d i then ht ▸ F i else fun _=>0
  refine ⟨⟨axes,G⟩,fun i=>?_,hG⟩
  change oneCharted (axes i (d i)) _
  unfold axes
  rw [dif_pos rfl]
  exact hF i

theorem sizedCharts (ht : v.bank) (i:s.T) (h : imagePlanRank (s.pin i.val).sp≤K) :
    ∃ d:Stakes K,oneCharted (v.cAxes i (toRates d)) (s.pin i.val).sp := by
  let d (j:Nodes):=dim (oneEffectivePins (oneEndpointPrimalPins (s.pin i.val).sp) j)
  have hd j : d j<K^2+1:=Nat.lt_of_le_of_lt
    ((one_effective_dimension _ j).trans (by gcongr)) (Nat.lt_succ_self _)
  exact ⟨fun j=>⟨d j,hd j⟩,ht.1 i⟩

theorem issueTicket (x y : OneUnit p n N) (i j:s.T) (ha : apart s.T)
    (hx : x∈i.val) (hy : y∈j.val) (ht : v.bank)
    (hca : (onePinClosure p n).close (s.pin i.val).sp=(s.pin i.val).sp)
    (hcb : (onePinClosure p n).close (s.pin j.val).sp=(s.pin j.val).sp)
    (he : oneSecureAt s (x,y)) :
    ∃ k,OneOptions.ticket (s.pin i.val) (s.pin j.val) (v.mails i j k) x y := by
  obtain ⟨k,hk⟩:=ht.2 i j (oneCrossMatrix x y)
  have hpa : s.rooting x=(s.pin i.val).sp:=
    congrArg ImagePin.sp (s.poller_eq ha i.property hx)
  have hpb : s.rooting y=(s.pin j.val).sp:=
    congrArg ImagePin.sp (s.poller_eq ha j.property hy)
  obtain ⟨hA,hB⟩:=he
  change onePinSafe (oneEndpointPrimalPins (s.rooting x)) (oneChannelPins (s.rooting y)) x y at hA
  change onePinSafe (oneEndpointPrimalPins (s.rooting y)) (oneChannelPins (s.rooting x)) y x at hB
  rw [hpa,hpb] at hA hB
  have hf:=one_fits_table_reciprocal _ _ _ _ hk
  simp_rw [one_cross_reciprocal] at hf
  exact ⟨k,one_fits_safe _ _ hca _ _ hk (one_safe_actual _ _ x y hA),
    one_fits_safe _ _ hcb _ _ hf (one_safe_actual _ _ y x hB),hk⟩

variable {q:Format} {d e:Rates} (w:Typus p q d e)

def news (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.chances w (v.cAxes i d) (v.cAxes j e) (s.pin i.val) (s.pin j.val) (v.mails i j k) K
def frontPage (m:Mixer p n) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.notified m (s.pin i.val) (s.pin j.val) (v.mails i j k) (v.news w i j k)
def backPage (m:Mixer p n) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneOptions.notified m (s.pin j.val) (s.pin i.val) (fun e=>(v.mails i j k e)ᵀ) (v.news w i j k)
def leftSales (m:Mixer p n) (μ:Wgt (OneUnit p n N)) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneQuill.oneGoodSales w.qA w.t w.z (s.pin i.val).sp K (partW μ i.val)
    (v.frontPage w m i j k) m (v.cAxes i d)
def rightSales (m:Mixer p n) (μ:Wgt (OneUnit p n N)) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  OneQuill.oneGoodSales w.qB w.t w.z (s.pin j.val).sp K (partW μ j.val)
    (v.backPage w m i j k) m (v.cAxes j e)
def matchScore (m:Mixer p n) (μ:Wgt (OneUnit p n N)) (i j:s.T) (k:Fin (2^oneDeckMax p K)):=
  overlap (unifOn (oneOwnPart (N:=N) w.t w.z)) (v.leftSales w m μ i j k) (v.rightSales w m μ i j k)
def arena (m:Mixer p n) (μ:Wgt (OneUnit p n N)) (k:Fin (2^oneDeckMax p K)):=
  avg (pairW (portionW μ s.T) (portionW μ s.T))
    (fun x=>v.matchScore w m μ x.1 x.2 k)

end OneStation
end
end Lax793645Proofs.Simplifications
