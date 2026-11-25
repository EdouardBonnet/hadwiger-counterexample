import Lax793645Proofs.Simplifications.OnePredictionExactification
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionClasses

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Finset PredictionClass
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {N M : ℕ}

/-- Transport only the coordinates of the reference keys. The sampled
one-frame orientations and their laws are not changed. -/
def oneAugurCoordinates (g : OneAugur p N) : Augur p N:=
  fun l q x=>g l q ((oneAtomSplit l N).symm x)

theorem one_tab_reference_coordinates (g : OneAugur p N) (l : Tag p.g) (q r : F) :
    oneTabRef p l q g r=tabRef p l q (oneAugurCoordinates g) r := by
  unfold oneTabRef oneLawOmega
  rw [mapW_pr]
  rfl

def oneAssembly (g : Bool→OneAugur p N) (i j : Bool) (s t : F) : OneAugur p N:=
  fun l q x=>s*g i l q x+t*g j l q x

def oneRecital (c : PredictionClass) (g : Bool→OneAugur p N) (α : Party) (τ : ℝ):=
  c.recital p (fun i=>oneAugurCoordinates (g i)) α τ

theorem one_recital_echoes {c : PredictionClass} {g : Bool→OneAugur p N}
    {α : Party} {τ : ℝ} (h : oneRecital c g α τ)
    (i j : Bool) (s t r : F) (he : s*firstBit α i=t*firstBit α j)
    (hr : ∀ l q,oneTabRef p l q (oneAssembly g i j s t) r≤τ) : c.echoes i j s t := by
  apply h.2 i j s t r he
  intro l q
  have ha : oneAugurCoordinates (oneAssembly g i j s t)=
      PredictionClass.assembly (fun i=>oneAugurCoordinates (g i)) i j s t := by
    funext l q x
    rfl
  rw [←ha,←one_tab_reference_coordinates]
  exact hr l q

abbrev OneSeason (p : Shape) (M : ℕ):=∀ n,OneAugur p (M*n)

def oneDisappearing (U : Ultrafilter ℕ) (g : OneSeason p M) (r : F):=
  ∀ l q,slight (U:Filter ℕ) (fun n=>oneTabRef p l q (g n) r)

/-- Finite prediction-class separation applies unchanged to the physical
one-frame keys. Exactification uses the new unary concentration theorem. -/
theorem one_examine (U : Ultrafilter ℕ) (p : Shape) (M : ℕ)
    (g : Bool→OneSeason p M) (α : Party) :
    ∃ (c : PredictionClass) (τ : ℝ),0<τ ∧
      (∀ᶠ n in U,oneRecital c (fun i=>g i n) α τ) ∧ c.lit α ∧
      (c=dusk → ∀ i,∃ r,oneDisappearing U (g i) r) := by
  obtain ⟨c,τ,hτ,hc,hl,hd⟩:=PredictionClass.examine U p M
    (fun i n=>oneAugurCoordinates (g i n)) α
  refine ⟨c,τ,hτ,hc,hl,?_⟩
  intro he i
  obtain ⟨r,hr⟩:=hd he i
  refine ⟨r,fun l q=>?_⟩
  simpa only [one_tab_reference_coordinates] using hr l q

end
end Lax793645Proofs.Simplifications
