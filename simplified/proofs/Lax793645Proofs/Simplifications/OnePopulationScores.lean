import Lax793645Proofs.Simplifications.OnePopulationLaws
import Lax793645Proofs.Simplifications.OneSimultaneousScores
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AggregateCostBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {pop:OneLeafMixture p n N}

namespace OneStation

def twilight {q:Format} {d e:Rates} (v:OneStation p n N K pop)
    (w:Typus p q d e) (m:Mixer p n) (k:Fin (2^oneDeckMax p K))
    (Y:OneSilhouette p N r) (i j:pop.T) (o:OneUnit p n N×OneUnit p n N):=
  ind (v.frontPage w m i j k o.1 ∧ v.backPage w m i j k o.2)*
    OneTypus.oneSupportConstellation w o.1 o.2 (v.cAxes i d) (v.cAxes j e) m Y

def eligiblePair (v:OneStation p n N K pop) (m:Mixer p n) (i j:OneAspect pop)
    (Y:OneSilhouette p N r) (a:ℝ):=
  ∃ k:OneScrip p K,(onePermission k.2.2) ∧ a≤v.twilight k.2.2 m k.2.1 Y i.1 j.1 (i.2,j.2)

theorem ship_cost (v:OneStation p n N K pop) (μ:Wgt (OneUnit p n N)) (m:Mixer p n)
    (i:OneScrip p K) (Y:OneSilhouette p N r):
    avg (oneCirque pop μ) (fun x=>v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2))=
      v.stratum i.2.2 m μ i.2.1 Y :=
  couplings (portionW μ pop.T) (fun i=>partW μ i.val) _

theorem ship_pos (v:OneStation p n N K pop) (m:Mixer p n) (i:OneScrip p K)
    (Y:OneSilhouette p N r) (h:(onePermission i.2.2)) (hp:1≤p.r) (hn:2*p.r≤n)
    (x:OneViewPair pop):
    0≤v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2) := by
  apply mul_nonneg (ind_nonneg _)
  exact OneTypus.one_support_constellation_nonneg i.2.2 (v.cAxes x.1.1 _) (v.cAxes x.2.1 _) m Y x.1.2 x.2.2

theorem prognosis (v:OneStation p n N K pop) (μ:Wgt (OneUnit p n N)) (m:Mixer p n)
    (Y:OneSilhouette p N r) {ε a C ζ:ℝ} (he:0≤ε) (ha:0<a)
    (hp:1≤p.r) (hn:2*p.r≤n) (hs:OneLead μ pop m C ζ K)
    (h:∀ i:OneScrip p K,(onePermission i.2.2) → v.stratum i.2.2 m μ i.2.1 Y≤ε):
    pr (oneCirque pop μ) (fun x=>v.eligiblePair m x.1 x.2 Y a)≤num (OneScrip p K)*(ε/a) := by
  have hv:IsLaw (oneCirque pop μ):=pairW_law (one_troupe_bill hs).1 (one_troupe_bill hs).1
  exact Lax793645.FiniteScores.large_score_probability _ ⟨hv.nz,hv.total⟩
    (fun i:OneScrip p K=>(onePermission i.2.2))
    (fun i x=>v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2))
    ε a he ha (fun i hi x=>v.ship_pos m i Y hi hp hn x)
    (fun i hi=>(v.ship_cost μ m i Y).le.trans (h i hi))

end OneStation

def oneSupportBudget (p:Shape) (K:ℕ) (η a:ℝ):=
  0<a ∧ ∀ k:OneScrip p K,a≤OneTypus.oneMomus k.2.2*
    η^Fintype.card (Messenger (toFormat k.1.1))

theorem one_engaged_budget (p:Shape) (K:ℕ) {η:ℝ} (h:0<η):
    ∃ a,oneSupportBudget p K η a := by
  exact one_finite_positive_min _ (fun i=>mul_pos
    (mul_pos (one_kappa_pos _) (one_kappa_pos _)) (pow_pos h _))

end
end Lax793645Proofs.Simplifications
