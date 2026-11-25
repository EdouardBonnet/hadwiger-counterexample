import Lax793645Proofs.Simplifications.LinearCellCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FinitePredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CommonPartitionRefinement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {T : Type}
open StatusAnalysis DualAnalysis

variable {p : Shape} {N r s K R : ℕ}

def LinearSilhouette (Y : Silhouette p N r) (K : ℕ) :=
  ∀ l,HasLinearCells (Y l) K

theorem linear_silhouette_constant (Y : ∀ l : Tag p.g,F→Fin r) :
    LinearSilhouette (fun l q (_ : AtomKey (p:=p) l N)=>Y l q) 0 :=
  fun l=>linear_cells_constant (Y l)

theorem linear_silhouette_duo {Y : Silhouette p N r} {X : Silhouette p N s}
    (hY : LinearSilhouette Y K) (hX : LinearSilhouette X R) :
    LinearSilhouette (duoY Y X) (K+R) := by
  intro l
  let dims (b : Bool) := if b then r else s
  let f : ∀ b : Bool,F→AtomKey (p:=p) l N→Fin (dims b) :=
    fun b=>match b with | true=>Y l | false=>X l
  let budget (b : Bool) := if b then K else R
  have hf : ∀ b,HasLinearCells (f b) (budget b) := by
    intro b
    cases b
    · exact hX l
    · exact hY l
  obtain ⟨a,ha,L,φ,hφ⟩:=linear_cells_bundle budget f hf
  have hsize : (∑ b,budget b)=K+R := by simp [budget]
  rw [hsize] at ha
  refine ⟨a,ha,L,fun q y=>finProdFinEquiv (φ q y true,φ q y false),?_⟩
  intro q x
  change finProdFinEquiv (Y l q x,X l q x)=_
  congr 1
  exact Prod.ext (congrFun (hφ q x) true) (congrFun (hφ q x) false)

theorem linear_silhouette_bundle [Fintype T] [DecidableEq T]
    (f : T→ℕ) (Y : ∀ t,Silhouette p N (f t)) (R : T→ℕ)
    (h : ∀ t,LinearSilhouette (Y t) (R t)) :
    LinearSilhouette (bundleY f Y) (∑ t,R t) := by
  intro l
  exact linear_cells_postprocess (linear_cells_bundle R (fun t=>Y t l) (fun t=>h t l))
    (fun _ x=>Fintype.equivFin _ x)

/-- Extraction via `fromPulse` preserves the explicit linear-coordinate
certificate. Later preparation must retain this certificate as well. -/
theorem linear_from_pulse {Y : Silhouette p N r} (hY : LinearSilhouette Y K)
    (f : Pulsar p r) : LinearAugur (StatusAnalysis.DualAnalysis.fromPulse Y f) K := by
  intro l
  exact linear_cells_postprocess (hY l) (fun q a=>f l q a)

end
end Lax793645Proofs.Simplifications
