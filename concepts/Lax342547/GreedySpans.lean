import Lax342547.SpanDeficits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

/-!
---
title: Greedy mode space exposure
type: lemma
---
Finite greedy ordering of actual subspaces has nonnegative decreasing span increments; tails retain the greedy property and their increment sum equals the dimension increase.
-/

namespace Lax342547.GreedySpans

open scoped BigOperators

noncomputable def gain {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : ℝ :=
  (Module.finrank K (W ⊔ S : Submodule K V) : ℝ)-Module.finrank K W

def Greedy {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → Prop
  | _, [] => True
  | W, i::l => (∀ j ∈ l, gain W (S j) ≤ gain W (S i)) ∧ Greedy S (W ⊔ S i) l

axiom gain_nonneg {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : 0 ≤ gain W S

axiom gain_le_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : gain W S ≤ Module.finrank K S

axiom gain_antitone {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W U : Submodule K V} (hWU : W ≤ U) (S : Submodule K V) :
    gain U S ≤ gain W S

axiom exists_greedy_order {K V ι : Type} [Field K] [DecidableEq ι] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (I : Finset ι) (W : Submodule K V) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = I ∧ Greedy S W l

noncomputable def spanAfter {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (S : ι → Submodule K V) : Submodule K V → List ι → Submodule K V
  | W, [] => W
  | W, i::l => spanAfter S (W ⊔ S i) l

noncomputable def increments {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) : Submodule K V → List ι → List ℝ
  | _, [] => []
  | W, i::l => gain W (S i)::increments S (W ⊔ S i) l

axiom increments_length {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    (increments S W l).length = l.length

axiom span_after_eq {K V ι : Type} [Field K] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    spanAfter S W l = W ⊔ l.toFinset.sup S

axiom increments_sum {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    (increments S W l).sum = (Module.finrank K (spanAfter S W l) : ℝ)-Module.finrank K W

axiom increments_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) (a : ℝ)
    (h : ∀ i ∈ l, gain W (S i) ≤ a) : ∀ x ∈ increments S W l, x ≤ a

axiom increments_nonneg {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    ∀ x ∈ increments S W l, 0 ≤ x

axiom greedy_decreasing {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (h : Greedy S W l) : (increments S W l).Pairwise (fun a b => b ≤ a)

axiom greedy_drop {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (h : Greedy S W l) (n : ℕ) : Greedy S (spanAfter S W (l.take n)) (l.drop n)

axiom increments_drop {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) (n : ℕ) :
    (increments S W l).drop n = increments S (spanAfter S W (l.take n)) (l.drop n)

end Lax342547.GreedySpans
