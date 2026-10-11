import Lax342547.UnitContainers
import Lax342547.EntropyContainers
import Lax342547.TerminalCuts
import Lax342547.UnitLaws

namespace Lax342547Proofs.UnitContainers
open Lax342547.UnitContainers

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging

/--
---
conclusion: Lax342547.UnitContainers.residual_feasible_iff
---
-/
theorem residual_feasible_iff {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R₀ : Ω → Ω → Prop) (M κ : ℝ) (R : Finset (Ω × Ω)) (ρ : Ω × Ω → ℝ) :
    ρ ∈ residual {σ | Feasible μ R₀ M κ σ} R ↔
      Feasible μ (fun x y => R₀ x y ∧ (x,y) ∈ R) M κ ρ := by
  classical
  constructor
  · rintro ⟨⟨hp,hl,hr,hc,hs⟩,hR⟩
    refine ⟨hp,hl,hr,hc,?_⟩
    intro xy hn
    by_cases h₀ : R₀ xy.1 xy.2
    · exact hR xy (by simpa [h₀] using hn)
    · exact hs xy h₀
  · rintro ⟨hp,hl,hr,hc,hs⟩
    refine ⟨⟨hp,hl,hr,hc,?_⟩,?_⟩
    · intro xy hn
      exact hs xy (fun h => hn h.1)
    · intro xy hn
      exact hs xy (by simpa using fun h : R₀ xy.1 xy.2 ∧ xy ∈ R => hn h.2)

/--
---
conclusion: Lax342547.UnitContainers.terminal_unit_exceptions
---
-/
theorem terminal_unit_exceptions {Ω : Type} [Fintype Ω]
    (μ : Ω → ℝ) (R₀ : Ω → Ω → Prop) (M κ : ℝ) (R : Finset (Ω × Ω))
    (hμ : ∀ x, 0 ≤ μ x) (hM : 0 < M) (hκ : 0 < κ)
    (hn : ¬ (residual {σ | Feasible μ R₀ M κ σ} R).Nonempty) :
    ∃ S : Ω → Prop, ∃ E : Ω → Ω → Prop,
      cellMass μ S < 1/M ∧ pairEventMass μ μ E < 1/κ ∧
      (∀ x y, R₀ x y → (x,y) ∈ R → S x ∨ S y ∨ E x y) := by
  have hn' : ¬ ∃ ρ, Feasible μ (fun x y => R₀ x y ∧ (x,y) ∈ R) M κ ρ := by
    rintro ⟨ρ,hρ⟩
    exact hn ⟨ρ,(Lax342547.UnitContainers.residual_feasible_iff μ R₀ M κ R ρ).mpr hρ⟩
  obtain ⟨S,E,hS,hE,hcover⟩ := Lax342547.TerminalCuts.terminal_cut
    μ (fun x y => R₀ x y ∧ (x,y) ∈ R) M κ hμ hM hκ hn'
  exact ⟨S,E,hS,hE,fun x y h₀ hR => hcover x y ⟨h₀,hR⟩⟩

/--
---
conclusion: Lax342547.UnitContainers.unit_container_family
---
-/
theorem unit_container_family {Ω : Type} [Fintype Ω] [Nonempty Ω]
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
      (∀ I : Finset (Ω × Ω), (∀ x ∈ I, ∀ y ∈ I, ¬ H x y) → ∃ R ∈ C, I ⊆ R) := by
  obtain ⟨C,hcount,hterminal,hcover⟩ := Lax342547.EntropyContainers.entropy_container_family
    {ρ | Feasible μ R₀ M κ ρ} (fun xy => μ xy.1*μ xy.2) H ε (Real.log κ) L
    (Lax342547.UnitLaws.feasible_compact μ R₀ M κ)
    (Lax342547.UnitLaws.feasible_convex μ R₀ M κ)
    (fun ρ hρ => hρ.1)
    (fun ρ hρ => Lax342547.UnitLaws.feasible_entropy_budget μ R₀ M κ ρ hμ hμpos hκ hρ)
    hε hε1 hL hsuper
  refine ⟨C,?_,?_,hcover⟩
  · simpa only [Fintype.card_prod,pow_two] using hcount
  · intro R hR
    exact Lax342547.UnitContainers.terminal_unit_exceptions μ R₀ M κ R hμ.1 hM hκ (hterminal R hR)

end Lax342547Proofs.UnitContainers
