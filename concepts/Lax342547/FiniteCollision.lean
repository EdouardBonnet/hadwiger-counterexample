import Lax342547.RecordCollision
import Lax342547.ParameterCellAveraging
import Lax342547.CollisionExponents

/-!
---
title: Finite accepted overlap to original hole mass
type: definition and theorem
---
Independent parameter laws, original key-indexed record partitions and a proved local cell bound give an actual-mass collision inequality. The quantitative discarded-cell term retains the key-space and record counts.
-/

namespace Lax342547.FiniteCollision

open Lax342547.RecordCollision Lax342547.KeyMeasures Lax342547.CellAveraging
open Lax342547.RetainedImages Lax342547.ParameterCellAveraging Lax342547.CollisionPruning

noncomputable def acceptedDensity {A Ω Q : Type} [Fintype A] [Fintype Ω]
    (p : A → ℝ) (ρ : Ω → ℝ) (key : A → Ω → Q) (accept : A → Ω → Prop) : Q → ℝ :=
  fun q => ∑ x, p x * keyMass ρ (key x) (accept x) q

axiom average_sub {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f g : A → B → ℝ) :
    average p q (fun x y => f x y - g x y) = average p q f - average p q g

axiom independent_key_overlap {A B ΩA ΩB Q : Type} [Fintype A] [Fintype B]
    [Fintype ΩA] [Fintype ΩB] [Fintype Q] [Nonempty Q]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop) :
    uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) =
    Fintype.card Q * average p q (fun x y => ∑ z,
      keyMass α (keyA x) (acceptA x) z * keyMass β (keyB y) (acceptB y) z)

axiom averaged_record_pruning {A B ΩA ΩB Q C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB]
    [Fintype Q] [Nonempty Q] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop) (τ : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1) (hτ : 0 ≤ τ) :
    uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) -
      Fintype.card Q * average p q (fun x y => retainedPairs
        (fun zc : Q × C => keyRecordMass α (keyA x) (recordA x y) (acceptA x) zc.1 zc.2)
        (fun zd : Q × D => keyRecordMass β (keyB y) (recordB y x) (acceptB y) zd.1 zd.2)
        (fun zc zd => zc.1 = zd.1) τ) ≤
      Fintype.card Q * (Fintype.card C + Fintype.card D : ℝ) * τ

axiom finite_collision_lower {A B ΩA ΩB Q C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB]
    [Fintype Q] [Nonempty Q] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (keyA : A → ΩA → Q) (keyB : B → ΩB → Q)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop)
    (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a ≤ 1) (hβsum : ∑ b, β b ≤ 1) (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hloc : ∀ x y zc zd, zc.1 = zd.1 →
      τ ≤ keyRecordMass α (keyA x) (recordA x y) (acceptA x) zc.1 zc.2 →
      τ ≤ keyRecordMass β (keyB y) (recordB y x) (acceptB y) zd.1 zd.2 → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA x a ∧ (keyA x a, recordA x y a) = zc))
          (conditionalLaw β (fun b => acceptB y b ∧ (keyB y b, recordB y x b) = zd)) H) :
    ε * (uniformOverlap (acceptedDensity p α keyA acceptA) (acceptedDensity q β keyB acceptB) -
      Fintype.card Q * (Fintype.card C + Fintype.card D : ℝ) * τ) / Fintype.card Q ≤
        pairEventMass α β H

end Lax342547.FiniteCollision
