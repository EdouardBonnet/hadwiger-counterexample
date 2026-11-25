import Lax793645Proofs.Simplifications.OneFinitePredictions
import Lax793645Proofs.Simplifications.LinearCellCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {T : Type} {p : Shape} {N r s K R : ℕ}

def oneDuoY (Y : OneSilhouette p N r) (X : OneSilhouette p N s) :
    OneSilhouette p N (r*s):=fun l q x=>finProdFinEquiv (Y l q x,X l q x)
def oneBundleY [Fintype T] [DecidableEq T] (f : T→ℕ) (Y : ∀ t,OneSilhouette p N (f t)) :
    OneSilhouette p N (Fintype.card (∀ t,Fin (f t))):=
  fun l q x=>Fintype.equivFin _ (fun t=>Y t l q x)

def OneLinearSilhouette (Y : OneSilhouette p N r) (K : ℕ) :=
  ∀ l,HasLinearCells (Y l) K

theorem one_linear_silhouette_constant (Y : ∀ l : Tag p.g,F→Fin r) :
    OneLinearSilhouette (fun l q (_ : OneAtomKey (p:=p) l N)=>Y l q) 0 :=
  fun l=>linear_cells_constant (Y l)

theorem one_linear_silhouette_duo {Y : OneSilhouette p N r} {X : OneSilhouette p N s}
    (hY : OneLinearSilhouette Y K) (hX : OneLinearSilhouette X R) :
    OneLinearSilhouette (oneDuoY Y X) (K+R) := by
  intro l
  let dims (b : Bool) := if b then r else s
  let f : ∀ b : Bool,F→OneAtomKey (p:=p) l N→Fin (dims b) :=
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

theorem one_linear_silhouette_bundle [Fintype T] [DecidableEq T]
    (f : T→ℕ) (Y : ∀ t,OneSilhouette p N (f t)) (R : T→ℕ)
    (h : ∀ t,OneLinearSilhouette (Y t) (R t)) :
    OneLinearSilhouette (oneBundleY f Y) (∑ t,R t) := by
  intro l
  exact linear_cells_postprocess (linear_cells_bundle R (fun t=>Y t l) (fun t=>h t l))
    (fun _ x=>Fintype.equivFin _ x)

/-- Extraction via `fromPulse` preserves the explicit linear-coordinate
certificate. Later preparation must retain this certificate as well. -/
theorem one_linear_from_pulse {Y : OneSilhouette p N r} (hY : OneLinearSilhouette Y K)
    (f : Pulsar p r) : OneLinearAugur (oneFromPulse Y f) K := by
  intro l
  exact linear_cells_postprocess (hY l) (fun q a=>f l q a)

end
end Lax793645Proofs.Simplifications
