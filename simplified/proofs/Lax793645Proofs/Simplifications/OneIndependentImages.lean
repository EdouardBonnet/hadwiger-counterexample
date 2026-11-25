import Lax793645Proofs.Simplifications.QuadraticRepeatedBounds
import Lax793645Proofs.Simplifications.OneQueryCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

theorem one_independent_network (g : Route (I×J) G) (m : Mixer p n)
    (A : NomQuery p n g) (hA : ∀ i,Injective (A i).mulVec) :
    oneDependentGram (N:=N) g m A=
      quadraticIndependentNetwork g (fun i=>pullM (A i) (A i) (selfM p n m.mixM)) := by
  funext x
  apply propext
  apply forall_congr'
  intro i
  have hker : (A i).mulVecLin.ker=⊥:=LinearMap.ker_eq_bot.mpr (hA i)
  change (_=_ ∧ _ ) ↔ (Injective _ ∧ _)
  rw [hker,LinearMap.ker_eq_bot]
  rfl

theorem one_independent_images (g : Route (I×J) G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3≤N)
    (A : NomQuery p n g) (hA : ∀ i,Injective (A i).mulVec) :
    mapW (oneForumLaw m N) (onePeek g A)=
      unifOn (quadraticIndependentNetwork g (fun i=>pullM (A i) (A i) (selfM p n m.mixM))) := by
  rw [one_law_peek g m hN,one_independent_network g m A hA]

def oneResultKey (v : Template p I) (o : OneUnit p n N) (x : Inputs p n I) : OneKeys v.t N:=
  oneVolleyKeys (v.draw x) v.t o

def oneHeatMap (v : Template p I) (o : OneUnit p n N) (w : I→Wgt (Knobs p.g n)) :
    Wgt (OneKeys v.t N):=mapW (prodW w) (oneResultKey v o)

theorem one_template_show (v : Template p J) (x : Inputs p n J) (o : OneUnit p n N) :
    onePeek (globPort p v.t v.aim) ((v.doubleP n).left x) (oneMerge o)=
      oneScatter v.t N (oneResultKey v o x) := by
  exact one_peek_keys v.t (v.draw x) o

end
end Lax793645Proofs.Simplifications
