import Lax342547.PreparedInjectionScale

/-!
---
title: Uniform early channel choice for actual accepting tables
type: theorem
---
The channel dimension is fixed before the polynomial accepting-mass
exponent, the ambient dimension, the unit law, and the adaptive marks.
All sixteen flags of each component are controlled on actual admissible
tables, paying the loss relative to their original accepting mass.
-/

namespace Lax342547.UniformTableInjection
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.PreparedInjection
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh Lax342547.RetainedImages
open Lax342547.RelativeEntropy
open scoped BigOperators
axiom exists_uniform_injection {Comp : Type} [Fintype Comp] [Nonempty Comp]
    (K Cs : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ,∀ c : ℕ,∃ N₀ : ℕ,∀ N p m : ℕ,N₀ ≤ N → p ≤ N/8 → m ≤ N/100 →
      ∀ (U I : Type) [Fintype U] [Fintype I] (E : Matrix (Fin p) (Fin p) Binary)
      [Nonempty (Frame (Fin p) (Fin h) (Fin N) E)]
      (ρ : U → ℝ) (P : U → Pin (Comp × Bool) (Fin 2 × (Fin p ⊕ Fin h)) (Fin N))
      (A : U → Fin 2 → Comp → Frame (Fin p) (Fin h) (Fin N) E)
      (accept : U → U → Prop) (CL CR : I → U → Prop) (keyL keyR : U → I)
      (T : ∀ a b,Table (P a) (P b)) (M : ℝ),
      Probability ρ → 0 ≤ M → M ≤ (2 : ℝ)^m →
      (Fintype.card I : ℝ) ≤ (2 : ℝ)^(Cs*N) →
      (∀ u,(P u).rank ≤ K) →
      (∀ i e f,push ρ (fun u => A u i e) f ≤
        M*weights (PMF.uniformOfFintype (Frame (Fin p) (Fin h) (Fin N) E)) f) →
      (∀ a b,accept a b ↔ CL (keyL b) a) → (∀ a b,accept b a ↔ CR (keyR b) a) →
      (∀ a b,accept a b → Admissible (T a b)
        Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation (A a) (A b)) →
      1/(N : ℝ)^c ≤ cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2) →
      cellMass (fun ab : U × U => ρ ab.1*ρ ab.2)
        (fun ab => accept ab.1 ab.2 ∧ ¬ Injecting (T ab.1 ab.2)) ≤
        ε*cellMass (fun ab : U × U => ρ ab.1*ρ ab.2) (fun ab => accept ab.1 ab.2)

end Lax342547.UniformTableInjection
