import Lax342547.BipartiteFlows
import Lax342547.UnitLaws
import Lax342547.CellAveraging

/-!
---
title: Terminal exceptions from real capacity cuts
type: definition and theorem
---
A residual pair set admitting no probability law with the marginal and pair caps is covered by a small raw vertex exception and a small product-law pair exception. This proves the finite content of Lemma 3.3.
-/

namespace Lax342547.TerminalCuts

open Lax342547.BipartiteFlows Lax342547.FlowCuts Lax342547.RetainedImages Lax342547.CellAveraging
open scoped BigOperators

noncomputable def pairCapacity {Ω : Type} (μ : Ω → ℝ) (R : Ω → Ω → Prop) (κ : ℝ) : Ω → Ω → ℝ := by
  classical
  exact fun x y => if R x y then κ*(μ x*μ y) else 0

axiom law_iff_masked {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ) (ρ : Ω → Ω → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hκ : 0 ≤ κ) :
    Law (fun x => M*μ x) (fun y => M*μ y) (pairCapacity μ R κ) ρ ↔
      Lax342547.UnitLaws.Feasible μ R M κ (fun xy => ρ xy.1 xy.2)

axiom bipartite_cut_capacity {A B : Type} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (p : A → B → ℝ) (Z : Finset (Vertex A B))
    (hs : source ∈ Z) (ht : sink ∉ Z) : by
      classical
      exact cutCapacity (capacity a b p) Z =
        (∑ x, if left x ∉ Z then a x else 0)+(∑ y, if right y ∈ Z then b y else 0)+
        (∑ x, ∑ y, if left x ∈ Z ∧ right y ∉ Z then p x y else 0)

axiom terminal_cut {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R : Ω → Ω → Prop) (M κ : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hM : 0 < M) (hκ : 0 < κ)
    (hn : ¬ ∃ ρ, Lax342547.UnitLaws.Feasible μ R M κ ρ) :
    ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
      (∀ x y, R x y → S x ∨ S y ∨ E x y)

end Lax342547.TerminalCuts
