/- Adapted from OpenAI's FiniteComparisonBounds (Apache-2.0).
The chart choices no longer carry sparse-label booths. -/
import Lax793645Proofs.Simplifications.AffineAggregateCost
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteComparisonBounds
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function Finset Module LinearMap Filter Template StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild
open scoped BigOperators Topology
noncomputable section
namespace AffineOptions
variable {p:Shape} {n N K M r s0:ℕ} {b:PreparationParameters}
variable {w:LeafMixture p n N} {m:Mixer p n}
theorem sickBound (U:Wgt (UnitType p n N)) (v:Station p n N b.pins w) (Y:Silhouette p N r)
    (h: Lead U w m b) (a ε δ τ:ℝ)
    (hp:Beams b m Y w U v a ε δ τ) :
    let P (i : Aspect p n N w):=¬gauze p δ δ Y m b.pins i.2
    pr (troupe w U) P ≤ τ ∧ pr (cirque w U) (fun x=> P x.1∨P x.2) ≤ τ+τ := by
  classical
  intro P
  let μ:=troupe w U; have hi:= (troupe_bill h)
  have hh :pr μ P ≤ τ := ((mapW_pr μ Prod.snd (fun i=>¬gauze p δ δ Y m b.pins i)).symm).trans_le
    (hi.2.symm ▸ hp.rare)
  refine ⟨hh,?_⟩
  apply (pr_or_le (pairW_law hi.1 hi.1).nz).trans
  refine add_le_add ?_ ?_
  · refine le_trans ?_ hh
    have h:= pairW_pr μ μ P (fun _=>True)
    have hl : IsLaw μ:=hi.1
    exact le_of_eq (by simpa [hl.total] using h)
  refine le_trans ?_ hh
  have h:=pairW_pr μ μ (fun _=> True) P
  have hl:IsLaw μ:=hi.1
  exact le_of_eq (by simpa [hl.total] using h)
structure Loupe (p : Shape) (n N K : ℕ) (s:LeafMixture p n N) where
   r : s.T → Stakes K

structure Shipped (w:LeafMixture p n N) (K:ℕ) (u:Station p n N K w) (t:Loupe p n N K w) : Prop where
   charts i: charted (u.cAxes i (toRates (t.r i))) (w.pin i.val).sp

theorem ready_loupe (w:LeafMixture p n N) (u:Station p n N b.pins w) (hu:u.bank)
    (h:AffineAnalyticParameters p M b s0) (he:∀ i:w.T,planRank (w.pin i.val).sp ≤ b.pins) :
    ∃ t,Shipped w b.pins u t := by
  classical
  choose d hd using fun i:w.T=>sizedCharts _ _ _ hu i (he i)
  exact ⟨⟨d⟩,⟨hd⟩⟩
variable (w:LeafMixture p n N) (L:Loupe p n N b.pins w) (t:Station p n N b.pins w)
def routeC {K} (w:LeafMixture p n N) (L:Loupe p n N K w) (t:Station p n N K w)
    (x:Aspect p n N w) :=
   t.cAxes x.1 (toRates (L.r x.1))
abbrev KAspect {p:Shape} {n N:ℕ} (w:LeafMixture p n N):=Aspect p n N w

set_option maxHeartbeats 800000 in
theorem routeLive (h:Shipped w b.pins t L) (m:Mixer p n)
    (H: AffineAnalyticParameters p M b s0) (hn:2*p.r≤n)
    (x:Aspect p n N w) (Y: Silhouette p N r)
    (δ:ℝ)(he:0<δ) (hk:planRank (w.pin x.1.val).sp ≤b.pins)
    (hp:gauze p δ δ Y m b.pins x.2) :
    reports p r (wisp p Y) (wake p Y m x.2 (routeC w L t x)) (trimBeta p b.pins) δ := by
  apply plume_reports p b.pins m Y (w.pin x.1.val).sp _ _ (h.charts x.1)
    _ hk H.enter.first.hG H.enter.first.hR hn δ he hp
  intro i; exact Nat.lt_succ_iff.mp (L.r x.1 i).isLt
end AffineOptions
end
end Lax793645Proofs.Simplifications
