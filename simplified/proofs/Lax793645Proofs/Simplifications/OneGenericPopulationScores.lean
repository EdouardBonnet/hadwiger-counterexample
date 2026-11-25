import Lax793645Proofs.Simplifications.OnePopulationScores
import Lax793645Proofs.Simplifications.OnePopulationLaws
import Lax793645Proofs.Simplifications.OneGenericSimultaneousScores
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AggregateCostBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N K r:ℕ} {pop:OneLeafMixture p n N}

namespace OneStation

def genericEligiblePair (v:OneStation p n N K pop) (m:Mixer p n) (i j:OneAspect pop)
    (Y:OneSilhouette p N r) (a:ℝ):=
  ∃ k:OneScrip p K,(oneGenericPermission k.2.2) ∧ a≤v.twilight k.2.2 m k.2.1 Y i.1 j.1 (i.2,j.2)

theorem generic_prognosis (v:OneStation p n N K pop) (μ:Wgt (OneUnit p n N)) (m:Mixer p n)
    (Y:OneSilhouette p N r) {ε a C ζ:ℝ} (he:0≤ε) (ha:0<a)
    (hp:1≤p.r) (hn:2*p.r≤n) (hs:OneLead μ pop m C ζ K)
    (h:∀ i:OneScrip p K,(oneGenericPermission i.2.2) → v.stratum i.2.2 m μ i.2.1 Y≤ε):
    pr (oneCirque pop μ) (fun x=>v.genericEligiblePair m x.1 x.2 Y a)≤num (OneScrip p K)*(ε/a) := by
  have hv:IsLaw (oneCirque pop μ):=pairW_law (one_troupe_bill hs).1 (one_troupe_bill hs).1
  exact Lax793645.FiniteScores.large_score_probability _ ⟨hv.nz,hv.total⟩
    (fun i:OneScrip p K=>(oneGenericPermission i.2.2))
    (fun i x=>v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2))
    ε a he ha (fun i hi x=>v.ship_pos m i Y hi.1 hp hn x)
    (fun i hi=>(v.ship_cost μ m i Y).le.trans (h i hi))

end OneStation

end
end Lax793645Proofs.Simplifications
