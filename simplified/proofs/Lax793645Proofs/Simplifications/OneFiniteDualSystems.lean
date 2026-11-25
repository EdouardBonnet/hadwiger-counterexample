import Lax793645Proofs.Simplifications.OneConditionalSignaturePositivity
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteDualSystems

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Template StatusAnalysis StatusAnalysis.DualAnalysis OneAppearance Filter Finset Matrix Function LinearMap Module
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {d : Rates}

def oneWisp (p : Shape) (Y : OneSilhouette p N r) : Terrain p r:=
  fun l q=>mapW (oneLawOmega p N l q) (Y l q)
def oneWake (p : Shape) (Y : OneSilhouette p N r) (m : Mixer p n) (o : OneUnit p n N)
    (s : Charts p n d) : Gazette p r d:=fun i x a=>oneReflected x Y i o m (s i) a

theorem one_plume_reports (p:Shape) (K :ℕ) (m:Mixer p n) (Y:OneSilhouette p N r)
    (s : ImagePlan (Comp p.g) (OneColumn p n)) (t:Charts p n d) (o:OneUnit p n N)
    (hs:oneCharted t s) (hh:∀ i,d i≤K^2) (h:imagePlanRank s≤K)
    (hg:3≤p.g) (hp:1≤p.r) (hn:2*p.r≤n) (δ:ℝ) (hδ:0<δ)
    (hY:oneGauze p δ δ Y m K o):
    reports p r (oneWisp p Y) (oneWake p Y m o t) (basebeta p K/2) δ := by
  constructor
  · intro i x hx k; exact oneReflectedLaw x Y (Appearance.witLaw hx hp hn) _ _ _ _ _
  · intro i x hx k; exact oneRefInk x Y _ _ _ _ _
  intro i x hx he k hk v
  obtain ⟨g,ha,hb,hc⟩:=generic_summary p hg x.l x.q v.1
  rw [←hx] at ha
  have hf:= oneDemonstrates x Y o (m:=m) (t i) K i k δ hδ g v.2 ha hb hp hn hk (hY _)
    (hh _) (hs i).2 (fun x=>le_trans (one_effective_rank s i _ (by rw [←(hs i).1]; exact mem_range_self _ _)) h)
  exact hf.trans (pr_mono (oneReflectedLaw x Y (Appearance.witLaw he hp hn) i o m (t i) k).nz
    (fun j hj=>hj.2.trans (Prod.ext hc rfl)))

end
end Lax793645Proofs.Simplifications
