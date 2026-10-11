import Lax342547.RecipeChannels

/-!
---
title: Simultaneous assembly of opposite endpoints and reciprocal unit roles
type: lemma
---
The two cross forms assemble all four families of barred channel changes. Each updated primal-to-channel map receives precisely its own correction; opposite endpoint channels and reciprocal-role changes contribute zero. The exact formulas cover both cross orientations and their flips.
-/

namespace Lax342547.ChannelAssembly

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys

noncomputable def assemble {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i) :
    CrossForms (Component (Tag k)) (Coordinate k n b degree) H :=
  { forward := fun e => F.forward e +
      (∑ z, channelChange (barred W P (U e) (e, true))
        (protectedChannel Q z (e, false)) (δ z e) z) +
      ∑ i, (channelChange (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false))
        (protectedChannel P i (e, true)) (ε' i e) i).flip
    reverse := fun e => F.reverse e +
      (∑ i, channelChange (barred (Lax342547.PairedRecipes.flip W) Q (U' e) (e, true))
        (protectedChannel P i (e, false)) (δ' i e) i) +
      ∑ z, (channelChange (barred W P (V e) (e, false))
        (protectedChannel Q z (e, true)) (ε z e) z).flip }

axiom channel_change_coordinate {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z j : Fin 2)
    (v : Nominal B H) (h : H) : by
      classical
      exact channelChange D S δ z v (channelEmbedding j (Pi.single h 1)) =
        if z = j then (δ (D.mkQ v)).val h else 0

axiom assembled_plus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullPlus (assemble W P Q U V U' V' F δ ε δ' ε') e i z = fullPlus F e i z +
      restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ z e) i

axiom assembled_minus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullMinus (assemble W P Q U V U' V' F δ ε δ' ε') e i z = fullMinus F e i z +
      restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε z e) i

axiom reciprocal_plus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullPlus (assemble W P Q U V U' V' F δ ε δ' ε').flip e z i = fullPlus F.flip e z i +
      restriction (barred (Lax342547.PairedRecipes.flip W) Q (U' e) (e, true)) (protectedChannel P i (e, false)) (δ' i e) z

axiom reciprocal_minus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullMinus (assemble W P Q U V U' V' F δ ε δ' ε').flip e z i = fullMinus F.flip e z i +
      restriction (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false)) (protectedChannel P i (e, true)) (ε' i e) z

end Lax342547.ChannelAssembly
