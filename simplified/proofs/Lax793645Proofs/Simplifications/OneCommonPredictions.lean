import Lax793645Proofs.Simplifications.OneJointKeyFiberLaws
import Lax793645Proofs.Simplifications.OneStatusQuadratics

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
variable {p : Shape} {n N : ℕ}

def oneMismatch (g : OneAugur p N) (w : Pdual p n) (l : Tag p.g)
    (s : Label p.b) (f : Flavor p.g) (o : OneOrient p n N) (y : Knobs p.g n):=
  w (useAtom p l s f y)≠g l (dialed p l f y) (oneAtomKeyValue o l s (lit f l y))

def onePostulates (o : OneOrient p n N) (g : OneAugur p N) (w : Pdual p n)
    (E : Finset (Label p.b)) (δ : ℝ):=
  ∀ s,s∉E→∀ l f,pr (spins p n) (oneMismatch g w l s f o)≤δ

def oneYoke (m : Mixer p n) (x : OneUnit p n N) (i : Bool) (u : Profile p n) (α : F):=
  oneInner x i+(Tsym m u+α • role p n)

def oneClaimed (x : OneUnit p n N) (g : Bool→OneAugur p N) (m : Mixer p n)
    (w : Bool→Profile p n) (α : Bool→F) (L : Bool→Finset (Label p.b)) (δ : ℝ):=
  ∀ i,onePostulates (x i) (g i) (oneYoke m x i (w i) (α i)) (L i) δ

end
end Lax793645Proofs.Simplifications
