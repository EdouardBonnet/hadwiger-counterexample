import Lax342547.ExactPins
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.SetTheory.Cardinal.Finite

/-!
---
title: Finite metadata and exact-image records for additional pins
type: definition and theorem
---
A coefficient choice determines finitely many nominal subspaces. A split
record contains that choice and all prescribed images on those spaces.
Its fiber fixes the new pins and can be joined to the previous pins.
-/

namespace Lax342547.MetadataPins

open Lax342547.MomentSpace Lax342547.ExactPins

def Images {Axis I : Type} (N : Type) (S : Axis → Submodule Binary (I → Binary)) :=
  ∀ a, S a →ₗ[Binary] (N → Binary)

noncomputable instance {Axis I N : Type} [Fintype Axis] [Fintype I] [Fintype N]
    (S : Axis → Submodule Binary (I → Binary)) : Fintype (Images N S) := by
  classical
  let : ∀ a, Finite (S a →ₗ[Binary] (N → Binary)) := fun a =>
    Finite.of_injective (fun f : S a →ₗ[Binary] (N → Binary) => (f : S a → N → Binary))
      DFunLike.coe_injective
  exact Fintype.ofFinite (∀ a, S a →ₗ[Binary] (N → Binary))

def Key {J Axis I : Type} (N : Type) (S : J → Axis → Submodule Binary (I → Binary)) :=
  Σ j, Images N (S j)

noncomputable instance {J Axis I N : Type} [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (S : J → Axis → Submodule Binary (I → Binary)) : Fintype (Key N S) :=
  inferInstanceAs (Fintype (Σ j, Images N (S j)))

def record {Ω J Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (o : Ω) : Key N S :=
  ⟨choice o, fun a => (A o a).comp (S (choice o) a).subtype⟩

def pin {J Axis I N : Type} {S : J → Axis → Submodule Binary (I → Binary)}
    (k : Key N S) : Pin Axis I N := ⟨S k.1, k.2⟩

axiom image_count {Axis I N : Type} [Fintype Axis] [Fintype I] [Fintype N]
    (S : Axis → Submodule Binary (I → Binary)) :
    Nat.card (Images N S) = 2 ^ ((∑ a, Module.finrank Binary (S a)) * Fintype.card N)

axiom key_count {J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (S : J → Axis → Submodule Binary (I → Binary)) (u : ℕ)
    (hu : ∀ j, ∑ a, Module.finrank Binary (S j a) ≤ u) :
    Nat.card (Key N S) ≤ Fintype.card J * 2 ^ (u * Fintype.card N)

axiom refined_fiber {Ω J Axis I N : Type} [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (choice : Ω → J)
    (S : J → Axis → Submodule Binary (I → Binary)) (u : ℕ)
    (hu : ∀ j, ∑ a, Module.finrank Binary (S j a) ≤ u)
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A) (o : Ω) (ho : o ∈ R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧ (pin (record A choice S o)).Extends P ∧
      P.rank ≤ P₀.rank + u ∧
      R ∩ {x | record A choice S x = record A choice S o} ⊆ P.event A

end Lax342547.MetadataPins
