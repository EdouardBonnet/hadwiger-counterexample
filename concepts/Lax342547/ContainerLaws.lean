import Lax342547.UnitLaws

/-!
---
title: Entropy progress for residual pair laws
type: lemma
---
Residual feasible families retain compactness and convexity. Supersaturation selects a heavy neighborhood, and deleting it increases the minimum entropy by the exact negative log support cost.
-/

namespace Lax342547.ContainerLaws

open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

noncomputable def residual {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U) : Set (U → ℝ) :=
  {ρ | ρ ∈ P ∧ ∀ x, x ∉ R → ρ x = 0}

noncomputable def neighborMass {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop) (v : U) : ℝ :=
  cellMass ρ (H v)

noncomputable def conflictMass {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop) : ℝ :=
  ∑ v, ρ v * neighborMass ρ H v

axiom residual_mono {U : Type} [Fintype U] (P : Set (U → ℝ)) (R T : Finset U)
    (hTR : T ⊆ R) : residual P T ⊆ residual P R

axiom residual_compact {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U)
    (hP : IsCompact P) : IsCompact (residual P R)

axiom residual_convex {U : Type} [Fintype U] (P : Set (U → ℝ)) (R : Finset U)
    (hP : Convex ℝ P) : Convex ℝ (residual P R)

axiom supported_mass {U : Type} [Fintype U] (ρ : U → ℝ) (R : Finset U)
    (hρ : Probability ρ) (hs : ∀ x, x ∉ R → ρ x = 0) : cellMass ρ (fun x => x ∈ R) = 1

axiom positive_support {U : Type} [Fintype U] (ρ : U → ℝ) (hρ : Probability ρ) :
    ∃ x, 0 < ρ x

axiom mass_complement {U : Type} [Fintype U] (ρ : U → ℝ) (S : U → Prop)
    (hρ : Probability ρ) : cellMass ρ (fun x => ¬ S x) = 1-cellMass ρ S

axiom support_mass_positive {U : Type} [Fintype U]
    (ρ σ : U → ℝ) (S : U → Prop) (hρ : Probability ρ) (hσ : Probability σ)
    (hs : ∀ x, ¬ S x → σ x = 0) (hfull : ∀ x, 0 < σ x → 0 < ρ x) :
    0 < cellMass ρ S

axiom heavy_neighbor {U : Type} [Fintype U] (ρ : U → ℝ) (H : U → U → Prop)
    (R : Finset U) (ε : ℝ) (hρ : Probability ρ) (hs : ∀ x, x ∉ R → ρ x = 0)
    (_hε : 0 < ε) (hmass : ε ≤ conflictMass ρ H) :
    ∃ v ∈ R, ε ≤ neighborMass ρ H v

axiom minimum_mono {U : Type} [Fintype U] (P : Set (U → ℝ)) (q ρ σ : U → ℝ)
    (R T : Finset U) (hTR : T ⊆ R) (hσ : σ ∈ residual P T)
    (hmin : ∀ τ ∈ residual P R, entropy ρ q ≤ entropy τ q) : entropy ρ q ≤ entropy σ q

axiom recording_entropy_increment {U : Type} [Fintype U]
    (P : Set (U → ℝ)) (q ρ σ : U → ℝ) (R : Finset U) (H : U → U → Prop) (v : U) (ε : ℝ)
    (hprob : ∀ τ ∈ P, Probability τ) (hconv : Convex ℝ P)
    (hρ : ρ ∈ residual P R) (hmin : ∀ τ ∈ residual P R, entropy ρ q ≤ entropy τ q)
    (hσ : σ ∈ residual P R ∧ ∀ x, H v x → σ x = 0)
    (_hε : ε < 1) (hheavy : ε ≤ neighborMass ρ H v) :
    -Real.log (1-ε) ≤ entropy σ q-entropy ρ q

end Lax342547.ContainerLaws
