import Lax342547.PairedRecipes
import Lax342547.KeySpans

/-!
---
title: Actual paired-witness key spaces satisfy the baseline hypotheses
type: lemma
---
At a component keep precisely the nominal primal rays belonging to
incident selected atoms. Their span has dimension at most twenty-eight,
is contained in the combined primal space, and is disjoint from every
table space when the labels avoid the sparse exclusions.
-/

namespace Lax342547.PairedKeys

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.NominalPrimal Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

abbrev Positions (W : Lists k n b degree r hr) := Σ i, Σ z, Fin (W.length i z)

def labels (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).label

def bases (W : Lists k n b degree r hr) (i : Fin 2) (x : Σ z, Fin (W.length i z)) :=
  (W.left i x.1 x.2).base

noncomputable def direction (W : Lists k n b degree r hr) (e : Component (Tag k))
    (x : Positions W) : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary := by
  classical
  exact if (W.left x.1 x.2.1 x.2.2).tag ∈ e.val then ray (labels W) (bases W) x else 0

def keys (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    Submodule Binary ((Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) :=
  Submodule.span Binary (Set.range (direction (H := H) W e))

axiom key_bounds [Fintype H] (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    keys (H := H) W e ≤ primal ∧ Module.finrank Binary (keys (H := H) W e) ≤ 28

axiom fresh_spans [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A) (hB : Excludes Q B)
    (hfresh : FreshAgainst W A B) :
    (∀ a, Disjoint (tableSpace P a) (keys (H := H) W a.1)) ∧
      ∀ a, Disjoint (tableSpace Q a) (keys (H := H) (flip W) a.1)

end Lax342547.PairedKeys
