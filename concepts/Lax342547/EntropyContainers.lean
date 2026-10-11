import Lax342547.EntropySelectors
import Lax342547.ContainerRun
import Lax342547.FingerprintCounts

/-!
---
title: Entropy bounded container families
type: lemma
---
Compact convex feasible laws with an entropy budget and uniform conflict supersaturation admit a finite family of infeasible containers covering every independent set. Ordered fingerprints obey the same exponential counting budget as the paper.
-/

namespace Lax342547.EntropyContainers

open Lax342547.RelativeEntropy Lax342547.ContainerLaws Lax342547.ContainerRun
open scoped BigOperators

axiom entropy_increment_positive (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : 0 < -Real.log (1-ε)

axiom entropy_fingerprint_length {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ)
    (law : Finset U → U → ℝ) (pick : Finset U → U) (I R : Finset U) (fuel L : ℕ)
    (hprob : ∀ ρ ∈ P, Probability ρ) (hc : Convex ℝ P)
    (hb : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hspec : ∀ T, (residual P T).Nonempty →
      law T ∈ residual P T ∧ (∀ σ ∈ residual P T, entropy (law T) q ≤ entropy σ q) ∧
      pick T ∈ T ∧ ε ≤ neighborMass (law T) H (pick T) ∧ (∃ w ∈ T, H (pick T) w))
    (hL : B/(-Real.log (1-ε))+1 ≤ L) (hactive : (residual P R).Nonempty) :
    (run (fun T => (residual P T).Nonempty) pick H I fuel R).2.length ≤ L

axiom entropy_container_family {U : Type} [Fintype U] [Nonempty U]
    (P : Set (U → ℝ)) (q : U → ℝ) (H : U → U → Prop) (ε B : ℝ) (L : ℕ)
    (hcompact : IsCompact P) (hconvex : Convex ℝ P) (hprob : ∀ ρ ∈ P, Probability ρ)
    (hbudget : ∀ ρ ∈ P, 0 ≤ entropy ρ q ∧ entropy ρ q ≤ B)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hL : B/(-Real.log (1-ε))+1 ≤ L)
    (hsuper : ∀ ρ ∈ P, ε ≤ conflictMass ρ H) :
    ∃ C : Finset (Finset U),
      C.card ≤ (Fintype.card U+1)^L ∧
      (∀ R ∈ C, ¬ (residual P R).Nonempty) ∧
      (∀ I : Finset U, (∀ x ∈ I, ∀ y ∈ I, ¬ H x y) → ∃ R ∈ C, I ⊆ R)

end Lax342547.EntropyContainers
