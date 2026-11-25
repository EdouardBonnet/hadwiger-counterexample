import Lax793645Proofs.Simplifications.OneScalarOptions
import Lax793645Proofs.Simplifications.ExactSupportSpanStability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset Matrix LinearMap Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N r K : ℕ} {q : Format} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e} {β δ η : ℝ}

/-- The seven-generator construction starts from the original spans.
Polynomial continuation supplies all later deletion invariance. -/
theorem one_scalar_options_stable
    (hu : origami p r u δ) (hs : reports p r u s β δ) (ht : reports p r u t β δ)
    (hg : 3≤p.g) (hodd : Odd p.g) (hj : 1≤p.j) (hJ : 1≤p.J)
    (hlabels : 9*oneScalarBudget p K<Fintype.card (Label p.b))
    (hβ : 0<β) (hη : 0<η) (hsmall : playbook p K*η<1/2*β^2)
    (hd : ∀ i,d i≤K^2) (he : ∀ i,e i≤K^2)
    (hstable : ∀ i,∀ S : Straps (Label p.b),(∀ side,(S side).card≤oneScalarBudget p K)→
      (stellar u s t η ⊥ ⊥ i).band S=(stellar u s t η ⊥ ⊥ i).band ⊥)
    (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (haK : imagePlanRank a.sp≤K) (hbK : imagePlanRank b.sp≤K)
    (X : Charts p n d) (W : Charts p n e) (T : OneCross p n)
    (hA : oneCharted X a.sp) (hB : oneCharted W b.sp)
    (ha : oneTableSafe a.sp b.sp T) (hb : oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ)) :
    scorecard (chapter (stellar u s t η ⊥ ⊥) ⊥) (oneHailing X W T)→
      ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
        (s0 t0 : Script p (Messenger (toFormat q))),
        OneOptions.chances (g.binding p s0 t0) X W a b T K ∧
          ∀ i : Messenger (toFormat q),η≤circlet u s t (g i).1 i.1 (g i).2 := by
  classical
  obtain ⟨Pa⟩:=one_plan_protection_exists a.sp K (fun e=>(image_plan_component_dimension _ e).trans haK)
  obtain ⟨Pb⟩:=one_plan_protection_exists b.sp K (fun e=>(image_plan_component_dimension _ e).trans hbK)
  let U (side : Bool):=if side then Pa.selector else Pb.selector
  let D:=oneSelectorProtectionDim p K
  let C:=stellar u s t η ⊥ ⊥
  have hU (side : Bool) : dim (U side)≤D := by
    cases side
    · exact Pb.selector_dim
    exact Pa.selector_dim
  have hlabels' (i : Nodes) : ((⊥ : Stalls p) i).card+9*oneScalarBudget p K<
      Fintype.card (Label p.b) := by simpa using hlabels
  have hrich:=plenitude_at_budget (9*oneScalarBudget p K) hu hs ht hg ⊥ ⊥
    hlabels' hlabels' hβ hη hsmall hd he
  have hsupply (target : ∀ i,Suite d e i) (htarget : ∀ i,target i∈chapter C ⊥ i) :
      ∃ g,IndependentParade C U ⊥ target g Finset.univ := by
    apply independent_parade_of_stability C hj U D hU ⊥ (chapter C ⊥) ?_ ?_ target htarget
    · intro i S hS
      simpa only [bot_sup_eq,C,chapter] using hstable i S hS
    · intro i S hS y
      have hsize (side) : (S side).card≤9*oneScalarBudget p K := by
        have hh:=hS side
        change (S side).card≤oneScalarBudget p K at hh
        omega
      simpa only [bot_sup_eq] using hrich i S hsize y
  intro hv
  exact one_processions ⊥ ⊥ η a b X W T hA hB ha hb Pa Pb
    hg hodd hJ ⊥ hsupply hv

end
end Lax793645Proofs.Simplifications
