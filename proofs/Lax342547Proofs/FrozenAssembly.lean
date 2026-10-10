import Lax342547.FrozenAssembly
import Lax342547Proofs.GradientAssembly

namespace Lax342547Proofs.FrozenAssembly
open Lax342547.FrozenAssembly

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys
open Lax342547.FrozenBaselines Lax342547.RawBaselines Lax342547.ChannelAssembly

/--
---
conclusion: Lax342547.FrozenAssembly.flip_lists_twice
---
-/
theorem flip_lists_twice {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Lax342547.PairedRecipes.flip (Lax342547.PairedRecipes.flip W) = W := by
  cases W
  rfl

/--
---
conclusion: Lax342547.FrozenAssembly.barred_channel_frozen
---
-/
theorem barred_channel_frozen {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a c : Component (Tag k) × Bool) (z : Fin 2)
    (δ : (Nominal (Coordinate k n b degree) H ⧸ barred W P U a) →ₗ[Binary]
      perpendicular (protectedChannel Q z c))
    (v w : Nominal (Coordinate k n b degree) H)
    (h : v ∈ P.space a ⊔ keys W a.1 ∨ w ∈ Q.space c ⊔ keys (Lax342547.PairedRecipes.flip W) c.1) :
    channelChange (barred W P U a) (protectedChannel Q z c) δ z v w = 0 := by
  apply Lax342547Proofs.ChannelChanges.frozen
  rcases h with hv | hw
  · exact Or.inl (Submodule.mem_sup_left hv)
  · right
    obtain ⟨p, hp, key, hkey, heq⟩ := Submodule.mem_sup.mp hw
    have hkey0 : channelProjection z key = 0 := by
      ext h
      exact (Lax342547Proofs.PairedKeys.key_bounds (Lax342547.PairedRecipes.flip W) c.1).1 hkey z h
    rw [← heq, map_add, hkey0, add_zero]
    exact ⟨p, hp, rfl⟩


/--
---
conclusion: Lax342547.FrozenAssembly.assembled_frozen
---
-/
theorem assembled_frozen {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H] [Fintype N]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    {E : Moment k n b degree} (oA oB : Unit (H := H) (N := N) (E := E))
    (hF : Frozen F W P Q oA oB) : Frozen (assemble W P Q U V U' V' F δ ε δ' ε') W P Q oA oB := by
  classical
  intro e
  constructor
  · intro v w h
    have h₁ (z : Fin 2) := barred_channel_frozen W P Q (U e) (e, true) (e, false) z (δ z e) v w h
    have hswap : w ∈ Q.space (e, false) ⊔ keys (Lax342547.PairedRecipes.flip W) e ∨
        v ∈ P.space (e, true) ⊔ keys (Lax342547.PairedRecipes.flip (Lax342547.PairedRecipes.flip W)) e := by
      simpa only [flip_lists_twice] using h.symm
    have h₂ (i : Fin 2) := barred_channel_frozen (Lax342547.PairedRecipes.flip W) Q P (V' e)
      (e, false) (e, true) i (ε' i e) w v hswap
    change F.forward e v w + (∑ z, channelChange (barred W P (U e) (e, true))
      (protectedChannel Q z (e, false)) (δ z e) z v w) +
      (∑ i, channelChange (barred (Lax342547.PairedRecipes.flip W) Q (V' e) (e, false))
        (protectedChannel P i (e, true)) (ε' i e) i w v) = _
    simp only [h₁, h₂, Finset.sum_const_zero, add_zero]
    exact (hF e).1 v w h
  · intro v w h
    have hflip : v ∈ Q.space (e, true) ⊔ keys (Lax342547.PairedRecipes.flip W) e ∨
        w ∈ P.space (e, false) ⊔ keys (Lax342547.PairedRecipes.flip (Lax342547.PairedRecipes.flip W)) e := by
      simpa only [flip_lists_twice] using h
    have h₁ (i : Fin 2) := barred_channel_frozen (Lax342547.PairedRecipes.flip W) Q P (U' e)
      (e, true) (e, false) i (δ' i e) v w hflip
    have h₂ (z : Fin 2) := barred_channel_frozen W P Q (V e) (e, false) (e, true) z (ε z e) w v h.symm
    change F.reverse e v w + (∑ i, channelChange (barred (Lax342547.PairedRecipes.flip W) Q (U' e) (e, true))
      (protectedChannel P i (e, false)) (δ' i e) i v w) +
      (∑ z, channelChange (barred W P (V e) (e, false))
        (protectedChannel Q z (e, true)) (ε z e) z w v) = _
    simp only [h₁, h₂, Finset.sum_const_zero, add_zero]
    exact (hF e).2 v w h

end Lax342547Proofs.FrozenAssembly
