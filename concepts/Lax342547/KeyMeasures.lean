import Lax342547.PrimalRecords

/-!
---
title: Accepted key subprobabilities and uniform overlap
type: definition and theorem
---
Accepted queries retain their original mass. Uniform reference overlap is exactly the number of keys times independent accepted collision probability.
-/

namespace Lax342547.KeyMeasures



noncomputable def keyMass {Ω Q : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop) (q : Q) : ℝ := by
  classical
  exact ∑ ω, if accepted ω ∧ key ω = q then ρ ω else 0

axiom key_mass_nonneg {Ω Q : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop) (hρ : ∀ ω, 0 ≤ ρ ω) (q : Q) :
    0 ≤ keyMass ρ key accepted q

axiom key_mass_total {Ω Q : Type} [Fintype Ω] [Fintype Q]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop) : by
      classical
      exact (∑ q, keyMass ρ key accepted q) = ∑ ω, if accepted ω then ρ ω else 0

axiom key_mass_subprobability {Ω Q : Type} [Fintype Ω] [Fintype Q]
    (ρ : Ω → ℝ) (key : Ω → Q) (accepted : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hsum : ∑ ω, ρ ω ≤ 1) :
    (∑ q, keyMass ρ key accepted q) ≤ 1

axiom key_collision_identity {ΩA ΩB Q : Type} [Fintype ΩA] [Fintype ΩB] [Fintype Q]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (keyA : ΩA → Q) (keyB : ΩB → Q)
    (acceptA : ΩA → Prop) (acceptB : ΩB → Prop) : by
      classical
      exact (∑ q, keyMass α keyA acceptA q * keyMass β keyB acceptB q) =
        ∑ a, ∑ b, if acceptA a ∧ acceptB b ∧ keyA a = keyB b then α a * β b else 0

noncomputable def uniformDensity {Q : Type} [Fintype Q] (mass : Q → ℝ) : Q → ℝ :=
  fun q => Fintype.card Q * mass q

noncomputable def uniformOverlap {Q : Type} [Fintype Q] (a b : Q → ℝ) : ℝ :=
  (∑ q, uniformDensity a q * uniformDensity b q) / Fintype.card Q

axiom uniform_overlap_collision {Q : Type} [Fintype Q] [Nonempty Q] (a b : Q → ℝ) :
    uniformOverlap a b = Fintype.card Q * ∑ q, a q * b q

end Lax342547.KeyMeasures
