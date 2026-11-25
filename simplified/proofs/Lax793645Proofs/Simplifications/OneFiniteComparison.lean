import Lax793645Proofs.Simplifications.OneCommonScores
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteComparisonBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis StatusAnalysis.DualAnalysis
open Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K M r s0:ℕ} {q:PreparationParameters}
  {pop:OneLeafMixture p n N} {m:Mixer p n}

theorem one_sick_bound (μ:Wgt (OneUnit p n N)) (v:OneStation p n N K pop)
    (Y:OneSilhouette p N r) {C ζ a ε δ τ:ℝ} (h:OneLead μ pop m C ζ K)
    (hp:OneBeams m Y pop μ v a ε δ τ):
    let P (i:OneAspect pop):=¬oneGauze p δ δ Y m K i.2
    pr (oneTroupe pop μ) P≤τ ∧ pr (oneCirque pop μ) (fun x=>P x.1 ∨ P x.2)≤τ+τ := by
  intro P
  let u:=oneTroupe pop μ
  have hi:=one_troupe_bill h
  have hh:pr u P≤τ:=((mapW_pr u Prod.snd (fun i=>¬oneGauze p δ δ Y m K i)).symm).trans_le
    (hi.2.symm ▸ hp.rare)
  refine ⟨hh,?_⟩
  apply (pr_or_le (pairW_law hi.1 hi.1).nz).trans
  refine add_le_add ?_ ?_
  · refine le_trans ?_ hh
    have ht:=pairW_pr u u P (fun _=>True)
    have hl:IsLaw u:=hi.1
    exact le_of_eq (by simpa [hl.total] using ht)
  · refine le_trans ?_ hh
    have ht:=pairW_pr u u (fun _=>True) P
    have hl:IsLaw u:=hi.1
    exact le_of_eq (by simpa [hl.total] using ht)

structure OneLoupe (pop:OneLeafMixture p n N) (K:ℕ) where
  r:pop.T→Stakes K

structure OneShipped (pop:OneLeafMixture p n N) (K:ℕ)
    (v:OneStation p n N K pop) (t:OneLoupe pop K):Prop where
  charts i:oneCharted (v.cAxes i (toRates (t.r i))) (pop.pin i.val).sp

theorem one_ready_loupe (v:OneStation p n N K pop) (hv:v.bank)
    (he:∀ i:pop.T,imagePlanRank (pop.pin i.val).sp≤K):
    ∃ t,OneShipped pop K v t := by
  classical
  choose d hd using fun i:pop.T=>v.sizedCharts hv i (he i)
  exact ⟨⟨d⟩,⟨hd⟩⟩

def oneRouteC (t:OneLoupe pop K) (v:OneStation p n N K pop) (x:OneAspect pop):=
  v.cAxes x.1 (toRates (t.r x.1))

theorem one_route_live (v:OneStation p n N K pop) (t:OneLoupe pop K)
    (h:OneShipped pop K v t) (m:Mixer p n) (hg:3≤p.g) (hr:1≤p.r) (hn:2*p.r≤n)
    (x:OneAspect pop) (Y:OneSilhouette p N r) (δ:ℝ) (hd:0<δ)
    (hk:imagePlanRank (pop.pin x.1.val).sp≤K) (hp:oneGauze p δ δ Y m K x.2):
    reports p r (oneWisp p Y) (oneWake p Y m x.2 (oneRouteC t v x)) (trimBeta p K) δ := by
  apply one_plume_reports p K m Y (pop.pin x.1.val).sp _ _ (h.charts x.1)
    _ hk hg hr hn δ hd hp
  intro i
  exact Nat.lt_succ_iff.mp (t.r x.1 i).isLt

end
end Lax793645Proofs.Simplifications
