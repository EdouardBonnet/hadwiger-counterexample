import Lax342547.GradientAssembly

/-!
---
title: The simultaneous gradient corrections retain every frozen pin and key entry
type: definition and theorem
---
Barred domains kill frozen pins and keys on the changed side. Opposite pin projections are annihilated by the permitted outputs, and opposite keys have zero channel coordinates. The assembled cross forms therefore retain all frozen entries simultaneously.
-/

namespace Lax342547.FrozenAssembly

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys
open Lax342547.FrozenBaselines Lax342547.RawBaselines Lax342547.ChannelAssembly

axiom flip_lists_twice {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Lax342547.PairedRecipes.flip (Lax342547.PairedRecipes.flip W) = W

axiom barred_channel_frozen {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a c : Component (Tag k) × Bool) (z : Fin 2)
    (δ : (Nominal (Coordinate k n b degree) H ⧸ barred W P U a) →ₗ[Binary]
      perpendicular (protectedChannel Q z c))
    (v w : Nominal (Coordinate k n b degree) H)
    (h : v ∈ P.space a ⊔ keys W a.1 ∨ w ∈ Q.space c ⊔ keys (Lax342547.PairedRecipes.flip W) c.1) :
    channelChange (barred W P U a) (protectedChannel Q z c) δ z v w = 0

axiom assembled_frozen {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H] [Fintype N]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    {E : Moment k n b degree} (oA oB : Unit (H := H) (N := N) (E := E))
    (hF : Frozen F W P Q oA oB) : Frozen (assemble W P Q U V U' V' F δ ε δ' ε') W P Q oA oB

end Lax342547.FrozenAssembly
