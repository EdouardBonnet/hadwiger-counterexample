import Lax793645Proofs.Simplifications.LinearCellCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PreparationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
variable {p : Shape} {n N R S : ℕ} {b : PreparationParameters}
  {m : Mixer p n} {w : LeafMixture p n N} {U : Wgt (UnitType p n N)} {ε : ℝ}

/-- The prediction obstruction restricted to predictors using a common
bounded list of linear coordinates for each tag and both diagonal bits. -/
def linearPredicts (b : PreparationParameters) (p : Shape) (N : ℕ) {n : ℕ}
    (m : Mixer p n) (w : LeafMixture p n N) (U : Wgt (UnitType p n N))
    (R : ℕ) (ε : ℝ) :=
  ∃ g : Bool→Augur p N,(∀ i,LinearAugur (g i) R) ∧
    (0.000001:ℝ)≤pr (w.sap U) (fun x=>∃ z L α,b.seems p m w x g z L α ε)

theorem linear_predicts_predicts (h : linearPredicts b p N m w U R ε) :
    b.predicts p N m w U ε := by
  obtain ⟨g,_,hg⟩:=h
  exact ⟨g,hg⟩

theorem linear_predicts_mono (h : linearPredicts b p N m w U R ε) (hRS : R≤S) :
    linearPredicts b p N m w U S ε := by
  obtain ⟨g,hlin,hg⟩:=h
  exact ⟨g,fun i l=>linear_cells_mono (hlin i l) hRS,hg⟩

end
end Lax793645Proofs.Simplifications
