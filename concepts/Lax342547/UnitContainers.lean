import Lax342547.EntropyContainers
import Lax342547.TerminalCuts

/-!
---
title: Terminal containers for actual admissible unit laws
type: lemma
---
The entropy container family applies to the actual marginal and pair capacity constraints. Every terminal container has the vertex and pair exceptions of Lemma 3.3, with the explicit fingerprint count and no injectivity restriction on later sampled raw types.
-/

namespace Lax342547.UnitContainers

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging

axiom residual_feasible_iff {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R₀ : Ω → Ω → Prop) (M κ : ℝ) (R : Finset (Ω × Ω)) (ρ : Ω × Ω → ℝ) :
    ρ ∈ residual {σ | Feasible μ R₀ M κ σ} R ↔
      Feasible μ (fun x y => R₀ x y ∧ (x,y) ∈ R) M κ ρ

axiom terminal_unit_exceptions {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R₀ : Ω → Ω → Prop) (M κ : ℝ) (R : Finset (Ω × Ω))
    (hμ : ∀ x, 0 ≤ μ x) (hM : 0 < M) (hκ : 0 < κ)
    (hn : ¬ (residual {σ | Feasible μ R₀ M κ σ} R).Nonempty) :
    ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
      (∀ x y, R₀ x y → (x,y) ∈ R → S x ∨ S y ∨ E x y)

axiom unit_container_family {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (μ : Ω → ℝ) (R₀ : Ω → Ω → Prop) (H : (Ω × Ω) → (Ω × Ω) → Prop)
    (M κ ε : ℝ) (L : ℕ) (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x)
    (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (hL : Real.log κ/(-Real.log (1-ε))+1 ≤ L)
    (hsuper : ∀ ρ, Feasible μ R₀ M κ ρ → ε ≤ conflictMass ρ H) :
    ∃ C : Finset (Finset (Ω × Ω)),
      C.card ≤ (Fintype.card Ω^2+1)^L ∧
      (∀ R ∈ C, ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
        cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
        (∀ x y, R₀ x y → (x,y) ∈ R → S x ∨ S y ∨ E x y)) ∧
      (∀ I : Finset (Ω × Ω), (∀ x ∈ I, ∀ y ∈ I, ¬ H x y) → ∃ R ∈ C, I ⊆ R)

end Lax342547.UnitContainers
