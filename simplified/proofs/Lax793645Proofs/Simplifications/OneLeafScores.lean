import Lax793645Proofs.Simplifications.OneFullLinearPalettes
import Lax793645Proofs.Simplifications.OneFiniteSupportCalendar
import Lax793645Proofs.Simplifications.OneQueryMassBounds
import Lax793645Proofs.Simplifications.OnePairedCollisionBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p:Shape} {q:Format} {d e:Rates} {M K s0:ℕ}



theorem one_chart_status_bound {p : Shape} {n K : ℕ} {d : Rates}
    (pin : ImagePlan (Comp p.g) (OneColumn p n)) (s : Charts p n d)
    (hs : oneCharted s pin) (hpin : imagePlanRank pin≤K) :
    (∀ i,d i≤K^2) ∧ ∀ i j,totalRank (s i (Pi.single j 1))≤K := by
  constructor
  · intro i
    have hd:dim (Cell (d i))=dim (LinearMap.range (s i)):=
      (LinearEquiv.ofInjective (s i) (hs i).2).finrank_eq
    rw [(hs i).1] at hd
    have he:d i=dim (oneEffectivePins (oneEndpointPrimalPins pin) i):=by
      simpa only [dim_vec,Fintype.card_fin] using hd
    rw [he]
    exact (one_effective_dimension pin i).trans (Nat.pow_le_pow_left hpin 2)
  · intro i j
    apply (one_effective_rank pin i _ ?_).trans hpin
    rw [←(hs i).1]
    exact ⟨Pi.single j 1,rfl⟩
private theorem support_variation_instances {A:Type} (i j:Fintype A) (u v:Wgt A) :
    @varOne A i u v=@varOne A j u v := by
  cases Subsingleton.elim i j
  rfl

private theorem support_overlap_instances {A:Type} (i j k l:Fintype A)
    (P:A→Prop) (u v:Wgt A) :
    @overlap A i (@unifOn A j P) u v=@overlap A k (@unifOn A l P) u v := by
  cases Subsingleton.elim i k
  cases Subsingleton.elim j l
  rfl


namespace OneStation
variable {p : Shape} {q : Format} {d e : Rates} {M K s0 : ℕ}
def stratum {n N r:ℕ} {pop:OneLeafMixture p n N} (v:OneStation p n N K pop)
    (w:Typus p q d e) (m:Mixer p n) (μ:Wgt (OneUnit p n N))
    (k:Fin (2^oneDeckMax p K)) (Y:OneSilhouette p N r):=
  avg (pairW (portionW μ pop.T) (portionW μ pop.T))
    (fun l=>OneTypus.oneSupportFilteredScore w (partW μ l.1.val) (partW μ l.2.val)
      (v.frontPage w m l.1 l.2 k) (v.backPage w m l.1 l.2 k)
      (v.cAxes l.1 d) (v.cAxes l.2 e) m Y)

/-- The support comparison applies to the actual prepared leaves and pair-dependent acceptance filters. -/
theorem score_calendar (w:Typus p q d e) (hw:(onePermission w))
    (h:OneUnaryParameters p M K s0) (C ε:ℝ) (hε:0<ε) :
    ∃ r coords:ℕ,∃ θ σ:ℝ,0<θ ∧ 0<σ ∧ ∀ᶠ n:ℕ in atTop,
      ∀ m:Mixer p n,reducedBinaryGood m → Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (pop:OneLeafMixture p n (M*n)) (μ:Wgt (OneUnit p n (M*n))) (ζ:ℝ),
        oneLeafStrength pop μ m C ζ K → IsLaw μ → 0<pop.amount μ →
        pop.within (oneFrameSide m) →
      ∀ v:OneStation p n (M*n) K pop,
      ∃ X:OneSilhouette p (M*n) r,OneFullLinearSilhouette X coords ∧
      ∀ s T (Y:OneSilhouette p (M*n) s),OneFullLinearSilhouette Y T → OneRefines Y X →
      ∀ θ' η:ℝ,θ'≤θ →
        pr (pop.sap μ) (fun o=>¬oneGauze p θ' η Y m K o)≤σ/2 →
        pr (pop.sap μ) (fun o=>¬oneLitFire o)≤σ/2 →
      ∀ k:Fin (2^oneDeckMax p K),v.arena w m μ k≤σ →v.stratum w m μ k Y≤ε := by
  obtain ⟨S,δ,θ,σ,hδ,hθ,hσ,hcal⟩:=
    OneTypus.one_finite_support_calendar w hw.2.1 hw.2.2.1 h (2*C) ε hε
  let A:ℝ:=num (Messenger q)+oneBaseProtectionDim p K
  have hrej:∀ᶠ n:ℕ in atTop,bp (A-n)≤δ := by
    have hlim: Tendsto (fun n:ℕ=>bp (A-n)) atTop (nhds 0):=by
      have hh:=(bp_nat_vanish (by norm_num : (0:ℝ)<1)).const_mul (bp A)
      simp only [mul_zero] at hh
      convert hh using 1
      funext n
      rw [←bp_add]
      congr 1
      ring
    exact hlim.eventually (eventually_le_nhds hδ)
  refine ⟨oneLinearPaletteSize (Messenger q) S,Fintype.card (Messenger q)*S,θ,σ,hθ,hσ,?_⟩
  filter_upwards [hcal,hrej,eventually_ge_atTop (2*p.r)]
    with n hn hrej hnR m hm hN pop μ ζ hp hμ hmass hframe v
  let u:=portionW μ pop.T
  let π (i:pop.T):=partW μ i.val
  obtain ⟨hu,hrebuild⟩:=rebuild hμ.nz hp.part (fun i hi=>(hp.leaf i hi).pos) hmass
  have hπ i:IsLaw (π i):=on_law hμ.nz (hp.leaf i.val i.property).pos
  have hcap i o:π i o≤bp ((2*C)*(M*n:ℕ))*oneUnitRaw m (M*n) o:=by
    have hc:=(hp.leaf i.val i.property).density o
    dsimp only [π]
    convert hc using 2 <;> push_cast <;> ring
  obtain ⟨L,hL⟩:=hn m hm hN pop.T u hu π hπ hcap (fun i=>v.cAxes i d) (fun i=>v.cAxes i e)
  let X:=oneLinearKeyPalette w.t (L.comp (oneKeyCoordinatesMap w.t (M*n)))
  refine ⟨X,one_full_linear_key_palette _ _,fun s T Y hfull hY θ' η hθ' hgauge hfire k hover=>?_⟩
  have hκA i:IsLaw (w.qA.policies w.t w.z n i):=
    Appearance.witLaw (w.qA.allure_apt w.t w.z hw.2.1 i) h.hR hnR
  have hκB i:IsLaw (w.qB.policies w.t w.z n i):=
    Appearance.witLaw (w.qB.allure_apt w.t w.z hw.2.2.1 i) h.hR hnR
  have hred (l:pop.T×pop.T):=v.sales_rejection w m μ l.1 l.2 k (hπ _) (hπ _) hκA hκB
  have hvarA (l:pop.T×pop.T):varOne
      (oneSales w.qA w.t w.z (π l.1) (v.frontPage w m l.1 l.2 k) m (v.cAxes l.1 d))
      (v.leftSales w m μ l.1 l.2 k)≤δ:=
    (support_variation_instances _ _ _ _).trans_le ((hred l).2.2.1.trans hrej)
  have hvarB (l:pop.T×pop.T):varOne
      (oneSales w.qB w.t w.z (π l.2) (v.backPage w m l.1 l.2 k) m (v.cAxes l.2 e))
      (v.rightSales w m μ l.1 l.2 k)≤δ:=
    (support_variation_instances _ _ _ _).trans_le ((hred l).2.2.2.trans hrej)
  have hover' : avg (pairW u u) (fun l=>overlap (unifOn (oneOwnPart w.t w.z))
      (v.leftSales w m μ l.1 l.2 k) (v.rightSales w m μ l.1 l.2 k))≤σ:=by
    refine (avg_congr fun l _=>?_).trans_le hover
    exact support_overlap_instances _ _ _ _ _ _ _
  apply hL s T Y hfull hY (fun l=>v.frontPage w m l.1 l.2 k) (fun l=>v.backPage w m l.1 l.2 k)
    (fun l o ho=>one_chart_status_bound (pop.pin l.1.val).sp (v.cAxes l.1 d)
      ho.1.2.1.1 (hp.leaf l.1.val l.1.property).bound)
    (fun l o ho=>one_chart_status_bound (pop.pin l.2.val).sp (v.cAxes l.2 e)
      ho.1.2.2.1 (hp.leaf l.2.val l.2.property).bound)
    (fun l=>v.leftSales w m μ l.1 l.2 k) (fun l=>v.rightSales w m μ l.1 l.2 k)
    (fun l=>(hred l).1) (fun l=>(hred l).2.1)
    (fun l=>(support_variation_instances _ _ _ _).trans_le (hvarA l))
    (fun l=>(support_variation_instances _ _ _ _).trans_le (hvarB l))
    (by refine (avg_congr fun l _=>?_).trans_le hover'; exact support_overlap_instances _ _ _ _ _ _ _)
  change pop.sap μ=mixW u π at hrebuild
  rw [←hrebuild]
  have hsap:=pop.sap_law hmass hμ
  apply (pr_mono_support (pop.sap μ) hsap.nz (fun o ho hbad=>show
      (¬oneGauze p θ' η Y m K o) ∨ ¬oneLitFire o from ?_)).trans
    ((pr_or_le hsap.nz).trans ((add_le_add hgauge hfire).trans_eq (by ring)))
  by_contra! hgood
  apply hbad
  refine ⟨pop.in_parent hframe (pop.present ho).1,?_,?_,hgood.2⟩
  · have hh:=OneQuill.one_gauze_area w.qA w.t w.z hw.2.1 Y o m θ' η hgood.1
    exact fun i=>(hh i).trans hθ'
  · have hh:=OneQuill.one_gauze_area w.qB w.t w.z hw.2.2.1 Y o m θ' η hgood.1
    exact fun i=>(hh i).trans hθ'

end OneStation

end
end Lax793645Proofs.Simplifications
