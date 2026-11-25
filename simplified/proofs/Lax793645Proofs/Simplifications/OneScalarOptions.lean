import Lax793645Proofs.Simplifications.OneOptionProcessions
import Lax793645Proofs.Simplifications.ScalablePlenitude

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild StatusAnalysis.Club
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N r K : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e} {β η δ : ℝ}

def oneScalarBudget (p : Shape) (K : ℕ) :=
  2^(oneSelectorProtectionDim p K+34)

set_option maxHeartbeats 1400000 in
/-- From the actual finite status-table hypotheses, produce protected
four-edge options whenever the stabilized scalar system is soluble.
The selector degree is required only to be at least one. -/
theorem one_scalar_options
    (h : origami p r u δ) (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hg : 3 ≤ p.g) (hodd : Odd p.g) (hj : 1 ≤ p.j) (hJ : 1 ≤ p.J)
    (A B : Stalls p)
    (hlabelsA : ∀ i,(A i).card+9*oneScalarBudget p K < Fintype.card (Label p.b))
    (hlabelsB : ∀ i,(B i).card+9*oneScalarBudget p K < Fintype.card (Label p.b))
    (hβ : 0 < β) (hη : 0 < η) (hsmall : playbook p K*η < 1/2*β^2)
    (hd : ∀ i,d i ≤ K^2) (he : ∀ i,e i ≤ K^2)
    (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (haK : imagePlanRank a.sp ≤ K) (hbK : imagePlanRank b.sp ≤ K)
    (X : Charts p n d) (W : Charts p n e) (T : OneCross p n)
    (hA : oneCharted X a.sp) (hB : oneCharted W b.sp)
    (ha : oneTableSafe a.sp b.sp T) (hb : oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ)) :
    ∃ H : Straps (Label p.b),sizeB H (8*oneScalarBudget p K) ∧
      (scorecard (chapter (stellar u s t η A B) H) (oneHailing X W T) →
        ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
          (s0 t0 : Script p (Messenger (toFormat q))),
          OneOptions.chances (g.binding p s0 t0) X W a b T K ∧
            ∀ i : Messenger (toFormat q),η ≤ circlet u s t (g i).1 i.1 (g i).2) := by
  classical
  obtain ⟨Pa⟩ := one_plan_protection_exists a.sp K (fun e=>(image_plan_component_dimension _ e).trans haK)
  obtain ⟨Pb⟩ := one_plan_protection_exists b.sp K (fun e=>(image_plan_component_dimension _ e).trans hbK)
  let U (side : Bool) := if side then Pa.selector else Pb.selector
  let D := oneSelectorProtectionDim p K
  have hU (side : Bool) : dim (U side) ≤ D := by
    cases side
    · exact Pb.selector_dim
    exact Pa.selector_dim
  have hrich := plenitude_at_budget (9*oneScalarBudget p K)
    h hs ht hg A B hlabelsA hlabelsB hβ hη hsmall hd he
  obtain ⟨H,hH,hsupply⟩ := independent_stable_supply (stellar u s t η A B) hj U D hU hrich
  exact ⟨H,hH,fun hv => one_processions A B η a b X W T hA hB ha hb Pa Pb
    hg hodd hJ H hsupply hv⟩

end
end Lax793645Proofs.Simplifications
