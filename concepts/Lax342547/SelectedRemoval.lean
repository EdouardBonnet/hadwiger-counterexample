import Lax342547.SelectedScalars

/-!
---
title: Subtracting selected atoms preserves pure annihilation
type: definition and theorem
---
Both factors of an incident selected atom are frozen keys. Every pure
quotient response therefore kills that atom. Linear combinations of
the selected atoms can be subtracted from the pair of cut profiles
while preserving every pure-response annihilation test.
-/

namespace Lax342547.SelectedRemoval

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PureObstructions

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

noncomputable def selectedPart (W : Lists k n b degree r hr)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) : Fin 2 → Profile k n b degree :=
  fun i => ∑ u, c i u • (W.left i u.1 u.2).profile

axiom atom_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) :
    Annihilates W P U V (Pi.single i (W.left i u.1 u.2).profile)

axiom selected_part_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P U V (selectedPart W c)

axiom subtract_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P U V (x - selectedPart W c)

end Lax342547.SelectedRemoval
