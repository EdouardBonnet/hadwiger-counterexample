import Lax793645Proofs.Simplifications.OneLeafScores

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {p:Shape} {M K s0:ℕ}

theorem one_finite_positive_min {A:Type} [Fintype A] (x:Wgt A) (hx:∀ i,0<x i) :
    ∃ ε:ℝ,0<ε ∧ ∀ i,ε≤x i := by
  cases isEmpty_or_nonempty A
  next h=>exact ⟨1,zero_lt_one,fun i=>(h.false i).elim⟩
  next h=>
    let f:=Finset.univ.image x
    have hf:f.Nonempty:=Finset.image_nonempty.mpr Finset.univ_nonempty
    obtain ⟨i,hi,ht⟩:=Finset.mem_image.mp (Finset.min'_mem f hf)
    exact ⟨f.min' hf,ht ▸ hx i,fun i=>Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ i))⟩

namespace OneStation

def bullseye {q:Format} {d e:Rates} {n N r:ℕ} {pop:OneLeafMixture p n N}
    (v:OneStation p n N K pop) (w:Typus p q d e) (m:Mixer p n)
    (μ:Wgt (OneUnit p n N)) (X:OneSilhouette p N r) (ε θ σ:ℝ):=
  ∀ s T (Y:OneSilhouette p N s),OneFullLinearSilhouette Y T → OneRefines Y X → ∀ θ' η:ℝ,θ'≤θ →
    pr (pop.sap μ) (fun o=>¬oneGauze p θ' η Y m K o)≤σ/2 →
    pr (pop.sap μ) (fun o=>¬oneLitFire o)≤σ/2 →
    ∀ k:Fin (2^oneDeckMax p K),v.arena w m μ k≤σ → v.stratum w m μ k Y≤ε

theorem simultaneous_calendar (h:OneUnaryParameters p M K s0) (C ε:ℝ) (hε:0<ε) :
    ∃ r coords:ℕ,∃ θ σ:ℝ,0<θ ∧ 0<σ ∧ ∀ᶠ n:ℕ in atTop,
      ∀ m:Mixer p n,reducedBinaryGood m → Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (pop:OneLeafMixture p n (M*n)) (μ:Wgt (OneUnit p n (M*n))) (ζ:ℝ),
        oneLeafStrength pop μ m C ζ K → IsLaw μ → 0<pop.amount μ →
        pop.within (oneFrameSide m) →
      ∀ v:OneStation p n (M*n) K pop,
      ∃ X:OneSilhouette p (M*n) r,OneFullLinearSilhouette X coords ∧
        ∀ i:OneScrip p K,(onePermission i.2.2) → v.bullseye i.2.2 m μ X ε θ σ := by
  choose r coords θ σ hθ hσ hcal using
    (fun i:OneScrip p K=>show ∃ r coords:ℕ,∃ θ σ:ℝ,0<θ ∧ 0<σ ∧
      ∀ᶠ n:ℕ in atTop,∀ m:Mixer p n,reducedBinaryGood m →
      Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (pop:OneLeafMixture p n (M*n)) (μ:Wgt (OneUnit p n (M*n))) (ζ:ℝ),
        oneLeafStrength pop μ m C ζ K → IsLaw μ → 0<pop.amount μ →
        pop.within (oneFrameSide m) →
      ∀ v:OneStation p n (M*n) K pop,
      ∃ X:OneSilhouette p (M*n) r,OneFullLinearSilhouette X coords ∧
        ((onePermission i.2.2) → v.bullseye i.2.2 m μ X ε θ σ) from by
      by_cases hi:(onePermission i.2.2)
      · obtain ⟨r,coords,θ,σ,hθ,hσ,hc⟩:=score_calendar i.2.2 hi h C ε hε
        refine ⟨r,coords,θ,σ,hθ,hσ,?_⟩
        filter_upwards [hc] with n hn m hm hN pop μ ζ hp hμ hmass hframe v
        obtain ⟨X,hX,hF⟩:=hn m hm hN pop μ ζ hp hμ hmass hframe v
        exact ⟨X,hX,fun _=>hF⟩
      · exact ⟨1,0,1,1,zero_lt_one,zero_lt_one,Filter.Eventually.of_forall
          (fun n m hm hN pop μ ζ hp hμ hmass hframe v=>
            ⟨fun _ _ _=>0,one_full_linear_constant (fun _ _=>0),fun h=>(hi h).elim⟩)⟩)
  obtain ⟨θ0,hθ0,hθmin⟩:=one_finite_positive_min θ hθ
  obtain ⟨σ0,hσ0,hσmin⟩:=one_finite_positive_min σ hσ
  refine ⟨Fintype.card (∀ i:OneScrip p K,Fin (r i)),∑ i,coords i,θ0,σ0,hθ0,hσ0,?_⟩
  filter_upwards [eventually_all.mpr hcal] with n hn m hm hN pop μ ζ hp hμ hmass hframe v
  choose X hX hF using fun i=>hn i m hm hN pop μ ζ hp hμ hmass hframe v
  refine ⟨oneBundleY r X,one_full_linear_bundle r X coords hX,?_⟩
  intro i hi s T Y hfull hY θ' η hθ' hgauge hfire k hover
  exact hF i hi s T Y hfull (one_refines_trans hY (one_bundle_refines r X i)) θ' η
    (hθ'.trans (hθmin i)) (hgauge.trans (div_le_div_of_nonneg_right (hσmin i) (by norm_num)))
    (hfire.trans (div_le_div_of_nonneg_right (hσmin i) (by norm_num))) k
    (hover.trans (hσmin i))

end OneStation
end
end Lax793645Proofs.Simplifications
