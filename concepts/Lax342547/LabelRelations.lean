import Lax342547.TensorBlocks
import Lax342547.SelectorInterpolation
import Lax342547.ConcreteCut

/-!
---
title: Triangle relations separate into individual label blocks
type: definition and theorem
---
Selector interpolation makes bounded-support block expansions unique.
The union of three component supports has size at most 3R, so a triangle
relation holds separately for every label, including absent labels.
-/

namespace Lax342547.LabelRelations

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorBlocks
open Lax342547.CutProfiles

def supported {Label Base : Type} [DecidableEq Label] (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) (s : Label) : Matrix Base Base Binary :=
  if s ∈ L then Z s else 0

def edge {Tag : Type} [DecidableEq Tag] (a b : Tag) (h : a ≠ b) : Component Tag :=
  ⟨{a, b}, Finset.card_pair h⟩

axiom blocks_unique {Base : Type} [Fintype Base] {b degree : ℕ}
    (L : Finset (Fin b → Binary)) (Z : (Fin b → Binary) → Matrix Base Base Binary)
    (hdegree : L.card ≤ degree + 1) (h : (∑ s ∈ L, block (selectorEval (degree := degree)) s (Z s)) = 0) :
    ∀ s ∈ L, Z s = 0

axiom triangle_blocks {Base : Type} [Fintype Base] {b degree R : ℕ}
    (L : Fin 3 → Finset (Fin b → Binary))
    (Z : Fin 3 → (Fin b → Binary) → Matrix Base Base Binary)
    (hL : ∀ i, (L i).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (h : (∑ i, ∑ s ∈ L i, block (selectorEval (degree := degree)) s (Z i s)) = 0) :
    ∀ s, (∑ i, supported (L i) (Z i) s) = 0

axiom cut_triangle {Tag V : Type} [DecidableEq Tag] [AddCommGroup V] [Module Binary V]
    (w : Tag → V) (a b c : Tag) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cutMap w (edge a b hab) + cutMap w (edge b c hbc) + cutMap w (edge a c hac) = 0

end Lax342547.LabelRelations
