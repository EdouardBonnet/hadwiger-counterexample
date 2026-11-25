import Lax793645Proofs.Simplifications.OneGenericStatusContinuation
import Lax793645Proofs.Simplifications.OneExactPredictionCatalog

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset Matrix LinearMap Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N r R : ℕ}

theorem one_exact_span_catalog_control (Y : OneSilhouette p N r)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (K B : ℕ) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hp : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r)
    (hB : (B:ℝ)<bp ((p.b:ℝ)-2*p.j)) :
    ∃ H : Space (OneJointKey p N),dim H≤3*(p.g*R) ∧
      (∀ o o',OnePaletteGood H o→OnePaletteGood H o'→OneFullTableGap Y m K o o') ∧
      (∀ o : OneUnit p n N,OnePaletteGood H o→∀ d : Rates,∀ v : Charts p n d,
        (∀ i w,totalRank (v i w)≤K)→
        ∀ i E,E.card≤B→∀ w α f,
          ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E (yokeSet w α) f→
            OneTesterFree Y f ∧
            onePostulates (o i) (oneFromPulse Y f) (oneYoke m o i (v i w) α) ∅ 0) ∧
      ∀ o : OneUnit p n N,OnePaletteGood H o→OneGenericStatusContinues Y m B o := by
  obtain ⟨H,hH,hgap,hnorm⟩:=one_exact_catalog_control Y hY hN hsmall m K B hg h3 hj hp hn hroom hB
  obtain ⟨J,hJ,hcont⟩:=one_generic_status_continuation_control Y hY hN hsmall m B hp hn hB
  refine ⟨H⊔J,?_,?_,?_,?_⟩
  · have hd : dim (H⊔J : Space (OneJointKey p N))+dim (H⊓J : Space (OneJointKey p N))=
        dim H+dim J:=Submodule.finrank_sup_add_finrank_inf_eq H J
    omega
  · intro o o' ho ho'
    exact hgap o o' (one_palette_good_mono le_sup_left ho) (one_palette_good_mono le_sup_left ho')
  · intro o ho
    exact hnorm o (one_palette_good_mono le_sup_left ho)
  · intro o ho
    exact hcont o (one_palette_good_mono le_sup_right ho)

end
end Lax793645Proofs.Simplifications
