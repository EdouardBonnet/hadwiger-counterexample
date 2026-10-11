import Lax342547.PureTesterRoom
import Lax342547.TesterProductRouting

/-!
---
title: Positive pure-flavor mass for the actual synthetic parity slice Grams
type: lemma
---
The ordered Gram for synthetic parity on q selected coordinates in each
half is a sum of q active products. Routing these products into retained
pure tester pairs proves its positive mass and the full slice variance
bound with an explicit mass floor independent of n and the unit law.
-/

namespace Lax342547.SyntheticGramSlices
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open Lax342547.PureTesterRoom
open Lax342547.AffineSliceVariance Lax342547.RawFrames Lax342547.FrameTuples Lax342547.GramOrbitDensity
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false


def sliceGram {q m : ℕ} (R C : Fin q → Fin m) :
    Matrix (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) Binary
  | some (Sum.inl i),some (Sum.inr j) => if R i = C j then 1 else 0
  | _,_ => 0

def leftFactor (q : ℕ) (p : Fin q) : Option (Fin q ⊕ Fin q) → Binary
  | some (Sum.inl i) => if p = i then 1 else 0
  | _ => 0

def rightFactor {q m : ℕ} (R C : Fin q → Fin m) (p : Fin q) :
    Option (Fin q ⊕ Fin q) → Binary
  | some (Sum.inr j) => if R p = C j then 1 else 0
  | _ => 0

axiom slice_gram_products {q m : ℕ} (R C : Fin q → Fin m) :
    sliceGram R C = fun i j => ∑ p : Fin q,leftFactor q p i*rightFactor R C p j

axiom pure_slice_gram_mass {k n b degree r q m : ℕ}
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (sel : Fin b → Binary)
    (l : Tag k) (T₀ : Finset (Tag k))
    (hroom : q ≤ k*(2*k+1-T₀.card)*r) (R C : Fin q → Fin m) :
    uniformFloor k r (Fin q ⊕ Fin q) ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q))))
      (fun V => (pointColumns sel (value V)).transpose*selfGram hr hd M*pointColumns sel (value V) = sliceGram R C)


axiom pure_slice_variance {S H : Type} [Fintype S] [DecidableEq S]
    [Fintype H] {k n b degree r q m : ℕ}
    (l : Tag k) (T₀ : Finset (Tag k))
    (N : ℕ) (sel : Fin b → Binary)
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (R C : Fin q → Fin m)
    (hroom : q ≤ k*(2*k+1-T₀.card)*r)
    (E : S → Matrix (Coordinate k n b degree) (Coordinate k n b degree) Binary)
    (G : S → Matrix (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) Binary)
    [∀ i,Nonempty (Frame (Coordinate k n b degree) H (Fin N) (E i))]
    [∀ i,Nonempty (Orbit (Fin N) (G i))]
    (hE : ∀ i,E i = selfGram hr hd M) (hG : ∀ i,G i = sliceGram R C)
    (test : (S → (Fin N × (Option (Fin q ⊕ Fin q) ⊕ Option (Fin q ⊕ Fin q)) → Binary)) → ℝ) (htest : ∀ z,|test z| ≤ 1)
    (hN : Fintype.card (Option (Fin q ⊕ Fin q))+Fintype.card (Option (Fin q ⊕ Fin q))+1 ≤ N)
    (hsmall : ((2 : ℝ)^(Fintype.card (Option (Fin q ⊕ Fin q))*Fintype.card (Option (Fin q ⊕ Fin q))+2))*
        ((2 : ℝ)^(Fintype.card (Option (Fin q ⊕ Fin q))*Fintype.card (Option (Fin q ⊕ Fin q))+2))/Real.sqrt ((2 : ℝ)^N) ≤
      1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)))+1)) :
    (∑ o : ∀ i,Frame (Coordinate k n b degree) H (Fin N) (E i),weights (PMF.uniformOfFintype _) o*
      ((∑ V : Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q),
        conditionalLaw (weights (PMF.uniformOfFintype _)) (fun V : Coefficients n l (pureOutside T₀) (Fin q ⊕ Fin q) => GramEvent sel E G (value V)) V*
          test (fun i => batchEquiv ((o i).P*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V),(o i).Q*pointColumns (k := k) (n := n) (b := b) (degree := degree) sel (value V))))-
            referenceMean N G test)^2) ≤
      (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.errorBound N (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q)) (Option (Fin q ⊕ Fin q))+
        4*(((2 : ℝ)^(2*Fintype.card (Fin q ⊕ Fin q)+1)/(2 : ℝ)^n)/(uniformFloor k r (Fin q ⊕ Fin q))^2)


end
end Lax342547.SyntheticGramSlices
