import Lax342547.BarredElimination
import Lax342547.TensorBlocks

/-!
---
title: Sparse residual contractions belong to the actual primal pins
type: lemma
---
Pure nominal quotient responses put a tested individual contraction in
the barred space. Unselected sparse labels eliminate its key and private
terms, so the contraction lies in the actual primal pin intersection.
`DerivativeResponses` pairs this membership with the actual derivative
tests and table injection flags in both reciprocal modes.
-/

namespace Lax342547.PrimalContractions

open Lax342547.MomentSpace Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.TensorAnnihilators Lax342547.ConcreteGeometry Lax342547.ProjectedPins
open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.SparsePins
open Lax342547.PinLabelExclusions Lax342547.BarredSpaces Lax342547.ResidualLabels

noncomputable def coordinates {B : Type} (ψ : Module.Dual Binary (B → Binary)) : B → Binary := by
  classical
  exact dualCoordinates ψ

axiom endpoint_vector {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (T : Submodule Binary (B → Binary)) (hE : E.map (primalProjection i) ≤ T)
    (ψ : Module.Dual Binary (B → Binary)) (hψ : T ≤ LinearMap.ker ψ) :
    primalEmbedding i ((M i).mulVecLin (coordinates ψ)) ∈ D

axiom sparse_contraction {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary)
    (v : Coord × Base → Binary) :
    (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)).mulVecLin v =
      ∑ s ∈ L, Lax342547.SparsePins.labelTensor p s
        (fun a => ∑ c, p s c.1 * Z s a c.2 * v c)

axiom unselected_pin_contraction {k n b degree r R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k))
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U j))
    (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, true)) (barred W P V (e, false)))
    (i : Fin 2) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : M i = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    (M i).mulVecLin (coordinates ψ) ∈ pinnedPrimal P i (e, true)

axiom unselected_pin_contraction_mode {k n b degree r R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (p : Bool) (U V : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k))
    (hU : ∀ j, IsCompl (protectedChannel P j (e, p)) (U j))
    (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, p)) (barred W P V (e, !p)))
    (i : Fin 2) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : M i = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : projected P i (e, !p) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    (M i).mulVecLin (coordinates ψ) ∈ pinnedPrimal P i (e, p)

end Lax342547.PrimalContractions
