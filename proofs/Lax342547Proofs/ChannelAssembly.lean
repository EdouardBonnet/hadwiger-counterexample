import Lax342547.ChannelAssembly
import Lax342547.ChannelChanges

namespace Lax342547Proofs.ChannelAssembly
open Lax342547.ChannelAssembly

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys

/--
---
conclusion: Lax342547.ChannelAssembly.channel_change_coordinate
---
-/
theorem channel_change_coordinate {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z j : Fin 2)
    (v : Nominal B H) (h : H) : by
      classical
      exact channelChange D S δ z v (channelEmbedding j (Pi.single h 1)) =
        if z = j then (δ (D.mkQ v)).val h else 0 := by
  classical
  by_cases hz : z = j
  · subst j
    rw [if_pos rfl]
    exact Lax342547.ChannelChanges.channel_entry D S δ z v h
  · rw [if_neg hz]
    have hp : channelProjection (B := B) z (channelEmbedding j (Pi.single h 1)) = 0 := by
      ext a
      simp [channelProjection, channelEmbedding, hz]
    change dotProduct (δ (D.mkQ v)).val (channelProjection z (channelEmbedding j (Pi.single h 1))) = 0
    rw [hp, dotProduct_zero]

/--
---
conclusion: Lax342547.ChannelAssembly.assembled_plus
---
-/
theorem assembled_plus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullPlus (assemble W P Q U V U' V' F δ ε δ' ε') e i z = fullPlus F e i z +
      restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ z e) i := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  change F.forward e (primalEmbedding i v) (channelEmbedding z (Pi.single h 1)) +
    (∑ j, channelChange (barred W P (U e) (e, true))
      (protectedChannel Q j (e, false)) (δ j e) j (primalEmbedding i v) (channelEmbedding z (Pi.single h 1))) +
    (∑ j, channelChange (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false))
      (protectedChannel P j (e, true)) (ε' j e) j (channelEmbedding z (Pi.single h 1)) (primalEmbedding i v)) = _
  simp only [Lax342547.ChannelAssembly.channel_change_coordinate, Lax342547.ChannelChanges.opposite_primal,
    Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single z]
  · simp only
    rfl
  · intro j _ hj
    simp only [if_neg hj]
  · simp


/--
---
conclusion: Lax342547.ChannelAssembly.assembled_minus
---
-/
theorem assembled_minus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullMinus (assemble W P Q U V U' V' F δ ε δ' ε') e i z = fullMinus F e i z +
      restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε z e) i := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  simp [fullMinus, assemble, restriction, LinearMap.BilinForm.flip,
    LinearMap.BilinForm.flipHom, Lax342547.ChannelAssembly.channel_change_coordinate,
    Lax342547.ChannelChanges.opposite_primal]
  fin_cases z <;> simp


/--
---
conclusion: Lax342547.ChannelAssembly.reciprocal_plus
---
-/
theorem reciprocal_plus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullPlus (assemble W P Q U V U' V' F δ ε δ' ε').flip e z i = fullPlus F.flip e z i +
      restriction (barred (Lax342547.PairedRecipes.flip W) Q (U' e) (e, true)) (protectedChannel P i (e, false)) (δ' i e) z := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  simp [fullPlus, CrossForms.flip, assemble, restriction, LinearMap.BilinForm.flip,
    LinearMap.BilinForm.flipHom, Lax342547.ChannelAssembly.channel_change_coordinate,
    Lax342547.ChannelChanges.opposite_primal]
  fin_cases i <;> simp

/--
---
conclusion: Lax342547.ChannelAssembly.reciprocal_minus
---
-/
theorem reciprocal_minus {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (e : Component (Tag k)) (i z : Fin 2) :
    fullMinus (assemble W P Q U V U' V' F δ ε δ' ε').flip e z i = fullMinus F.flip e z i +
      restriction (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false)) (protectedChannel P i (e, true)) (ε' i e) z := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  simp [fullMinus, CrossForms.flip, assemble, restriction, LinearMap.BilinForm.flip,
    LinearMap.BilinForm.flipHom, Lax342547.ChannelAssembly.channel_change_coordinate,
    Lax342547.ChannelChanges.opposite_primal]
  fin_cases i <;> simp

end Lax342547Proofs.ChannelAssembly
