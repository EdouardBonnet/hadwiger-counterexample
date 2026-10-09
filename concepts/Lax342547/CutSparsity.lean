import Lax342547.CutProfiles
import Mathlib.Data.Fintype.Card

/-!
---
title: Majority normalization of sparse cut profiles
type: definition and theorem
---
Counting unequal unordered tag pairs forces a strict majority whenever
four times the cut support is smaller than the square of the tag count.
Subtracting its common value gives a unique majority-zero representative.
-/

namespace Lax342547.CutSparsity

open Lax342547.MomentSpace Lax342547.CutProfiles

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

def UnequalPairs (w : Tag → V) := {p : Tag × Tag // w p.1 ≠ w p.2}

def NonzeroCuts (w : Tag → V) := {e : Component Tag // cutMap w e ≠ 0}

noncomputable def cutSize (w : Tag → V) : ℕ := Nat.card (NonzeroCuts w)

noncomputable def valueCount (w : Tag → V) (c : V) : ℕ := Nat.card {t : Tag // w t = c}

noncomputable def supportSize (w : Tag → V) : ℕ := Nat.card {t : Tag // w t ≠ 0}

axiom unequal_card_le [Fintype Tag] (w : Tag → V) :
    Nat.card (UnequalPairs w) ≤ 2 * cutSize w

axiom exists_majority [Fintype Tag] (w : Tag → V)
    (h : 4 * cutSize w < Fintype.card Tag * Fintype.card Tag) :
    ∃ c : V, Fintype.card Tag < 2 * valueCount w c

axiom minority_bound [Fintype Tag] (w : Tag → V) (c : V)
    (h : Fintype.card Tag < 2 * valueCount w c) :
    Fintype.card Tag * Nat.card {t : Tag // w t ≠ c} ≤ 2 * cutSize w

axiom majority_unique [Fintype Tag] [Nonempty Tag] (w v : Tag → V)
    (hcut : cutMap w = cutMap v)
    (hw : Fintype.card Tag < 2 * valueCount w 0)
    (hv : Fintype.card Tag < 2 * valueCount v 0) : w = v

axiom exists_unique_normalized [Fintype Tag] [Nonempty Tag]
    (W : Tag → Submodule Binary V)
    (hW : ∀ S : Finset Tag, Fintype.card Tag < 2 * S.card →
      (⨅ t : {t // t ∈ S}, W t.val) ≤ ⨅ t, W t)
    (w : Tag → V) (hw : ∀ t, w t ∈ W t)
    (h : 4 * cutSize w < Fintype.card Tag * Fintype.card Tag) :
    ∃! v : Tag → V, (∀ t, v t ∈ W t) ∧ cutMap v = cutMap w ∧
      Fintype.card Tag < 2 * valueCount v 0 ∧
      Fintype.card Tag * supportSize v ≤ 2 * cutSize w

end Lax342547.CutSparsity
