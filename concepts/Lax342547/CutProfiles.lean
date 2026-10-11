import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Pi

/-!
---
title: Cut profiles and the constant kernel
type: lemma
---
A cut profile has one coordinate for each unordered pair of tags, equal
to the sum of its two representative values. In characteristic two,
two representatives of the same profile differ by a constant tuple.
For representatives in restricted spaces, that constant lies in their
intersection. This is the kernel assertion of Lemma 2.3.
-/

namespace Lax342547.CutProfiles

open Lax342547.MomentSpace

def Component (Tag : Type) := {e : Finset Tag // e.card = 2}

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

def cutMap : (Tag → V) →ₗ[Binary] (Component Tag → V) where
  toFun w e := ∑ t ∈ e.val, w t
  map_add' w v := by ext e; simp [Finset.sum_add_distrib]
  map_smul' c w := by ext e; simp [Finset.smul_sum]

def representatives (W : Tag → Submodule Binary V) : Submodule Binary (Tag → V) :=
  Submodule.pi Set.univ W

def cutSpace (W : Tag → Submodule Binary V) : Submodule Binary (Component Tag → V) :=
  (representatives W).map cutMap

axiom same_cut_iff [Nonempty Tag] (W : Tag → Submodule Binary V)
    (w v : Tag → V) (hw : ∀ t, w t ∈ W t) (hv : ∀ t, v t ∈ W t) :
    cutMap w = cutMap v ↔ ∃ c ∈ ⨅ t, W t, ∀ t, w t + v t = c

end Lax342547.CutProfiles
