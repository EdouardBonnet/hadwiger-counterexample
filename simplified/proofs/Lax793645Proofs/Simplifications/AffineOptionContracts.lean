import Lax793645Proofs.Simplifications.AffineQueryProtection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CompatibleOptionRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace AffineOptions
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates} {side : Bool}

def signed (w : Quill p q d side) (t : Tagging p (Messenger q))
    (x y : Pin p n N) (s : Charts p n d) (T : Cross p n) (K : ℕ) :=
  charted s x.sp ∧ affinePenSpace (w.pen t) x.sp (affineQorth K) K ∧
    still side w.amp s T ∧ tableInj x.sp y.sp T

def chances (w : Typus p q d e) (s : Charts p n d) (v : Charts p n e)
    (x y : Pin p n N) (T : Cross p n) (K : ℕ) :=
  w.permission ∧ signed w.qA w.t x y s T K ∧
    signed w.qB w.t y x v (reciprocal p T) K

/-- Input rejection is part of the unnormalized successful-query measure. -/
def sales (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (pin : Pin p n N) (K : ℕ)
    (μ : Wgt (UnitType p n N)) (P : UnitType p n N → Prop)
    (m : Mixer p n) (s : Charts p n d) : Wgt (Keys (p:=p) t N) :=
  Volley.hist (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o => P o ∧ affineAvoids ((w.pen t).draw x) pin.sp (affineQorth K) ∧
      w.deposit t z m o s x)

variable {pop : LeafMixture p n N} (v : Station p n N K pop) (w : Typus p q d e)

def news (i j : pop.T) (k : Fin (2^deckMax p K)) :=
  chances w (v.cAxes i d) (v.cAxes j e) (pop.pin i.val) (pop.pin j.val) (v.mails i j k) K
def frontPage (m : Mixer p n) (i j : pop.T) (k : Fin (2^deckMax p K)) :=
  notified m (pop.pin i.val) (pop.pin j.val) (v.mails i j k) (news v w i j k)
def backPage (m : Mixer p n) (i j : pop.T) (k : Fin (2^deckMax p K)) :=
  notified m (pop.pin j.val) (pop.pin i.val) (reciprocal p (v.mails i j k)) (news v w i j k)
def leftSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : pop.T)
    (k : Fin (2^deckMax p K)) :=
  sales w.qA w.t w.z (pop.pin i.val) K (partW μ i.val)
    (frontPage v w m i j k) m (v.cAxes i d)
def rightSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : pop.T)
    (k : Fin (2^deckMax p K)) :=
  sales w.qB w.t w.z (pop.pin j.val) K (partW μ j.val)
    (backPage v w m i j k) m (v.cAxes j e)
def matchScore (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : pop.T)
    (k : Fin (2^deckMax p K)) :=
  overlap (lawNu p N w.t w.z) (leftSales v w m μ i j k) (rightSales v w m μ i j k)
def arena (m : Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K)) :=
  avg (pairW (portionW μ pop.T) (portionW μ pop.T))
    (fun x => matchScore v w m μ x.1 x.2 k)

end AffineOptions

end
end Lax793645Proofs.Simplifications
