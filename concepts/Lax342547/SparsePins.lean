import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
---
title: A uniform label budget for all sparse pin vectors
type: definition and theorem
---
Lemma 5.3. Each projected pin space has dimension at most K. A single
set of at most 2 |E| K (R + 14) labels contains the nonzero support of
every expansion on at most R + 14 labels in any of these spaces.
The hypothesis on selector degree is the one used in the paper's proof.
-/

namespace Lax342547.SparsePins

open Lax342547.MomentSpace

variable {Label Coord Base : Type}

def labelTensor (p : Label → Coord → Binary) (s : Label) :
    (Base → Binary) →ₗ[Binary] (Coord × Base → Binary) where
  toFun z i := p s i.1 * z i.2
  map_add' z w := by ext i; exact mul_add _ _ _
  map_smul' a z := by ext i; exact mul_left_comm _ _ _

noncomputable def expansion (p : Label → Coord → Binary) :
    (Label →₀ (Base → Binary)) →ₗ[Binary] (Coord × Base → Binary) :=
  Finsupp.lsum Binary (labelTensor p)

axiom sparse_pin_labels {Base Component : Type} [Fintype Base] [Fintype Component]
    {b degree K R : ℕ}
    (U : Bool → Component → Submodule Binary (SelectorCoordinates b degree × Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Component * K * (R + 14) ∧
      ∀ sign e (c : (Fin b → Binary) →₀ (Base → Binary)),
        c.support.card ≤ R + 14 → expansion (selectorEval (degree := degree)) c ∈ U sign e →
        c.support ⊆ B

end Lax342547.SparsePins
