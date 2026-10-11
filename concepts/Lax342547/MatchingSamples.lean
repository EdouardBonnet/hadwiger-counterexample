import Lax342547.SampledGraph
import Lax342547.ConnectedMatching
import Mathlib.Data.Fintype.EquivFin

/-!
---
title: Matching occurrences and raw unit types
type: lemma
---
Every touching matching has an injective orientation on sample positions. Its raw unit types form an independent conflict set even when different matching edges have identical raw types.
-/

namespace Lax342547.MatchingSamples

open Lax342547.ConnectedMatching Lax342547.SampledGraph

noncomputable def oriented {V : Type} (e : Finset V) (he : e.card = 2) : Bool → V :=
  fun b => ((e.equivFinOfCardEq he).symm (if b then 1 else 0)).val

axiom oriented_mem {V : Type} (e : Finset V) (he : e.card = 2) (b : Bool) : oriented e he b ∈ e

axiom oriented_injective {V : Type} (e : Finset V) (he : e.card = 2) : Function.Injective (oriented e he)

axiom oriented_covers {V : Type} (e : Finset V) (he : e.card = 2) (v : V) (hv : v ∈ e) :
    ∃ b, oriented e he b = v

axiom matching_orientation_injective {V : Type} (G : SimpleGraph V) (M : Finset (Finset V))
    (hM : IsTouchingMatching G M) :
    Function.Injective (fun eb : M × Bool => oriented eb.1.val (hM.1 _ eb.1.property).1 eb.2)

axiom matching_unit_independence {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) :
    ∀ e f : M, ¬ (∀ i j : Bool,
      hole (sample (oriented e.val (hM.1 _ e.property).1 i))
        (sample (oriented f.val (hM.1 _ f.property).1 j)))

noncomputable def unitType {Ω : Type} {m : ℕ} (sample : Fin m → Ω)
    (e : Finset (Fin m)) (he : e.card = 2) : Ω × Ω :=
  (sample (oriented e he false),sample (oriented e he true))

def fourConflict {Ω : Type} (hole : Ω → Ω → Prop) (u v : Ω × Ω) : Prop :=
  hole u.1 v.1 ∧ hole u.1 v.2 ∧ hole u.2 v.1 ∧ hole u.2 v.2

axiom matching_unit_is_unit {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) (e : M) :
    ¬ hole (unitType sample e.val (hM.1 _ e.property).1).1
      (unitType sample e.val (hM.1 _ e.property).1).2

axiom unit_types_independent {Ω : Type} (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    {m : ℕ} (sample : Fin m → Ω) (M : Finset (Finset (Fin m)))
    (hM : IsTouchingMatching (sampleGraph hole hsymm sample) M) : by
      classical
      exact let I := Finset.univ.image (fun e : M => unitType sample e.val (hM.1 _ e.property).1)
        (∀ u ∈ I, ¬ hole u.1 u.2) ∧ (∀ u ∈ I, ∀ v ∈ I, ¬ fourConflict hole u v)

end Lax342547.MatchingSamples
