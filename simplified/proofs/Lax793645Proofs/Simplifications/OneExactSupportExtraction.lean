import Lax793645Proofs.Simplifications.OnePreparedStatusSupport
import Lax793645Proofs.Simplifications.ExactStatusPredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N c R : ℕ}

/-- The local scalar extraction for the actual construction. Full
palettes and the prepared rank event turn a dual obstruction directly
into exact common predictions on every possible status. -/
theorem one_exact_dual_predictions (hg : Odd p.g) (h3 : 3≤p.g)
    (hp : 1≤p.r) (hn : 2*p.r≤n)
    (Y : OneSilhouette p N c) (hY : OneFullLinearSilhouette Y R)
    (m : Mixer p n) (K : ℕ)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ o o' : OneUnit p n N,OnePaletteGood H o→OnePaletteGood H o'→
      ∀ d d' : Rates,∀ v : Charts p n d,∀ v' : Charts p n d',
      (∀ i,d i≤K^2)→(∀ i,d' i≤K^2)→
      (∀ i j,totalRank (v i (Pi.single j 1))≤K)→
      (∀ i j,totalRank (v' i (Pi.single j 1))≤K)→
      ∀ β δ η : ℝ,η≤bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))→
      origami p c (oneWisp p Y) δ→
      reports p c (oneWisp p Y) (oneWake p Y m o v) β δ→
      reports p c (oneWisp p Y) (oneWake p Y m o' v') β δ→
      ∀ A B : Stalls p,∀ S : Straps (Label p.b),∀ z : DualCoefficients d d',
      z.law (chapter (stellar (oneWisp p Y) (oneWake p Y m o v) (oneWake p Y m o' v') η A B) S)→
      ∀ i : Grid,
      (outstraps A S true i.1).card<Fintype.card (Label p.b)→
      (outstraps B S false i.2).card<Fintype.card (Label p.b)→
      ∃ f : Pulsar p c,
        ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i.1
          (outstraps A S true i.1) (leftChime z i) f ∧
        ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o' v') i.2
          (outstraps B S false i.2) (rightChime z i) f := by
  obtain ⟨H,hH,hgap⟩:=one_palette_support_space hg hp hn Y hY m K hN hsmall
  refine ⟨H,hH,?_⟩
  intro o o' ho ho' d d' v v' hd hd' hv hv' β δ η hη hu hs ht A B S z hz i hA hB
  have hc:=(one_table_gap_dual Y m K o o' (hgap o o' ho ho') v v' hd hd' hv hv').mono hη
  exact dual_exact_status_predictors hu hs ht hc A B S z hz i h3 hA hB

end
end Lax793645Proofs.Simplifications
