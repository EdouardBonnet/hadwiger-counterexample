import Lax342547.ResidualLabels
import Lax342547.SparseKeyCoefficients

/-!
---
title: Sparse unselected primal vectors in barred spaces lie in the pins
type: lemma
---
Fresh selected keys cannot appear in a pin decomposition of an unselected
sparse vector. Once the keys vanish, protected/private channel
complements force the private part to vanish as well. This establishes
the pin membership needed before testing the derivative table maps.
-/

namespace Lax342547.BarredElimination

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.PinLabelExclusions Lax342547.BarredSpaces Lax342547.ResidualLabels
open Lax342547.NominalPrimal Lax342547.SparsePins

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

axiom individual_keys_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (v : (Fin b → Binary) → Option (Base k n) → Binary)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (q : Vector k n b degree) (hq : q ∈ individualKeys W i a.1)
    (hpin : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) - q ∈ projected P i a) :
    q = 0

axiom private_primal_pin {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Comp × Bool)
    (hU : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (v : (Fin 2 × (B ⊕ H)) → Binary) (hv : v ∈ primal)
    (h : v ∈ P.space a ⊔ ⨆ i, (U i).map (channelEmbedding i)) :
    v ∈ P.space a

axiom sparse_barred {R : ℕ} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool)
    (hU : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (L : Fin 2 → Finset (Fin b → Binary)) (hL : ∀ i, (L i).card ≤ R)
    (hdisjoint : ∀ i, Disjoint (L i) (chosenLabels W i))
    (c : Fin 2 → (Fin b → Binary) → Option (Base k n) → Binary)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) (hv : v ∈ primal)
    (hvec : ∀ i, primalProjection i v = ∑ s ∈ L i, labelTensor selectorEval s (c i s))
    (h : v ∈ barred W P U a) : v ∈ P.space a

end Lax342547.BarredElimination
