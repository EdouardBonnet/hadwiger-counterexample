import Lax342547.ContainerLaws

/-!
---
title: Deterministic entropy and neighborhood selections
type: definition and theorem
---
Compact feasible residual laws have fixed entropy minimizers. Raw supersaturation supplies a deterministic residual unit with positive neighborhood mass, guaranteeing progress of fingerprint deletion.
-/

namespace Lax342547.EntropySelectors

open Lax342547.RelativeEntropy Lax342547.ContainerLaws Lax342547.RetainedImages
open scoped BigOperators

axiom heavy_neighbor_nonempty {U : Type} [Fintype U]
    (ρ : U → ℝ) (R : Finset U) (H : U → U → Prop) (v : U)
    (hs : ∀ x, x ∉ R → ρ x = 0) (hm : 0 < neighborMass ρ H v) : ∃ w ∈ R, H v w

axiom entropy_selectors {U : Type} [Fintype U] [Nonempty U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε : ℝ)
    (hc : IsCompact P) (hprob : ∀ ρ ∈ P, Probability ρ) (hε : 0 < ε)
    (hsuper : ∀ ρ ∈ P, ε ≤ conflictMass ρ H) :
    ∃ law : Finset U → U → ℝ, ∃ pick : Finset U → U,
      ∀ R, (residual P R).Nonempty →
        law R ∈ residual P R ∧
        (∀ σ ∈ residual P R, entropy (law R) q ≤ entropy σ q) ∧
        pick R ∈ R ∧ ε ≤ neighborMass (law R) H (pick R) ∧
        (∃ w ∈ R, H (pick R) w)

end Lax342547.EntropySelectors
