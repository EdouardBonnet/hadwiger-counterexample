import Lax342547.CellAveraging

/-!
---
title: Independent parameter averaging with opposite-dependent original cells
type: lemma
---
Record partitions may depend on opposite parameters. Average each unchanged retained cell pair under the independent parameter laws, and recover a lower bound for the original orientation-pair event.
-/

namespace Lax342547.ParameterCellAveraging

open Lax342547.CellAveraging Lax342547.RetainedImages

noncomputable def average {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → B → ℝ) : ℝ := ∑ x, ∑ y, p x * q y * f x y

axiom average_mono {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f g : A → B → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (h : ∀ x y, f x y ≤ g x y) :
    average p q f ≤ average p q g

axiom average_const {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) (c : ℝ) :
    average p q (fun _ _ => c) = c

axiom average_cell_pair_lower {A B ΩA ΩB C D : Type}
    [Fintype A] [Fintype B] [Fintype ΩA] [Fintype ΩB] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (α : ΩA → ℝ) (β : ΩB → ℝ)
    (recordA : A → B → ΩA → C) (recordB : B → A → ΩB → D)
    (acceptA : A → ΩA → Prop) (acceptB : B → ΩB → Prop)
    (valid : A → B → C → D → Prop) (H : ΩA → ΩB → Prop) (τ ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ y, q y = 1)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b) (hτ : 0 < τ)
    (hloc : ∀ x y c d, valid x y c d → τ ≤ recordMass α (recordA x y) (acceptA x) c →
      τ ≤ recordMass β (recordB y x) (acceptB y) d → ε ≤
        pairEventMass (conditionalLaw α (fun a => acceptA x a ∧ recordA x y a = c))
          (conditionalLaw β (fun b => acceptB y b ∧ recordB y x b = d)) H) :
    ε * average p q (fun x y => retainedPairs (recordMass α (recordA x y) (acceptA x))
      (recordMass β (recordB y x) (acceptB y)) (valid x y) τ) ≤ pairEventMass α β H

end Lax342547.ParameterCellAveraging
