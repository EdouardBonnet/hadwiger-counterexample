import Lax342547.PairedKeys
import Lax342547.NominalBaselines

/-!
---
title: Bounded baselines for both actual cross orientations
type: definition and theorem
---
For admissible tables and fresh paired lists, construct the two full
nominal cross forms simultaneously. Each retains the actual pin/key
entries, extends the whole table, and has the paper's 3K+28 bound in
both reciprocal primal-to-channel orientations.
-/

namespace Lax342547.RawBaselines

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.PairedKeys
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.ReferencePins
open Lax342547.NominalPrimal Lax342547.FrozenBaselines Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

def Frozen (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E)) : Prop :=
  ∀ e,
    ExtendsFrozen (P.space (e, true)) (keys W e) (Q.space (e, false)) (keys (flip W) e)
      ((rawForms oA oB).forward e) (F.forward e) ∧
    ExtendsFrozen (Q.space (e, true)) (keys (flip W) e) (P.space (e, false)) (keys W e)
      ((rawForms oA oB).reverse e) (F.reverse e)

def Bounded (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (K : ℕ) : Prop :=
  ∀ e z,
    Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂ primal.subtype
      (channelEmbedding z))) ≤ 3 * K + 28 ∧
    Module.finrank Binary (LinearMap.range ((F.forward e).flip.compl₁₂ primal.subtype
      (channelEmbedding z))) ≤ 3 * K + 28 ∧
    Module.finrank Binary (LinearMap.range ((F.reverse e).compl₁₂ primal.subtype
      (channelEmbedding z))) ≤ 3 * K + 28 ∧
    Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂ primal.subtype
      (channelEmbedding z))) ≤ 3 * K + 28

axiom raw_baselines (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A) (hB : Excludes Q B)
    (hfresh : FreshAgainst W A B) (K : ℕ) (hP : P.rank ≤ K) (hQ : Q.rank ≤ K)
    (oA oB : Unit (H := H) (N := N) (E := E)) (T : Table P Q)
    (hadmissible : Admissible T observation observation oA oB) :
    ∃ F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H,
      Extends F T ∧ Frozen F W P Q oA oB ∧ Bounded F K

end Lax342547.RawBaselines
