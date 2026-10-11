import Lax342547.RawToGraph

/-!
---
title: Sampled graph failure bound
type: lemma
---
The actual container exception tails bound the probability of a large connected matching under raw supersaturation.
-/

namespace Lax342547.GraphFailure

open Lax342547.RelativeEntropy Lax342547.UnitLaws Lax342547.ContainerLaws
open Lax342547.RetainedImages Lax342547.CellAveraging Lax342547.FiniteSampling
open Lax342547.GoodSamples Lax342547.MatchingSamples Lax342547.SampledGraph Lax342547.ConnectedMatching
open Lax342547.RawToGraph
open scoped BigOperators

axiom graph_from_container_exceptions {Ω : Type}
    (hole : Ω → Ω → Prop) (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (C : Finset (Finset (Ω × Ω))) (S : Finset (Ω × Ω) → Ω → Prop)
    (E : Finset (Ω × Ω) → Ω → Ω → Prop)
    (hcover : ∀ I : Finset (Ω × Ω), (∀ x ∈ I, ∀ y ∈ I, ¬ fourConflict hole x y) → ∃ R ∈ C, I ⊆ R)
    (hcuts : ∀ R ∈ C, ∀ x y, ¬ hole x y → (x,y) ∈ R → S R x ∨ S R y ∨ E R x y)
    {m : ℕ} (sample : Fin m → Ω) (k : ℕ) (hscale : 200*(k-1) < m)
    (hgood : ∀ R ∈ C, ¬ Bad (S R) (E R) k sample) :
    100*connectedMatchingNumber (sampleGraph hole hsymm sample) < m

axiom sample_failure_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (μ : Ω → ℝ) (hole : Ω → Ω → Prop)
    (hsymm : ∀ ⦃x y⦄, hole x y → hole y x) (hloop : ∀ x, ¬ hole x x)
    (M κ ε : ℝ) (m k L : ℕ)
    (hμ : Probability μ) (hμpos : ∀ x, 0 < μ x)
    (hM : 0 < M) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε < 1)
    (hL : Real.log κ/(-Real.log (1-ε))+1 ≤ L)
    (hscale : 200*(k-1) < m)
    (hsuper : ∀ ρ, Feasible μ (fun x y => ¬ hole x y) M κ ρ →
      ε ≤ conflictMass ρ (fourConflict hole)) :
    cellMass (productLaw (fun _ : Fin m => μ))
      (fun sample => m ≤ 100*connectedMatchingNumber (sampleGraph hole hsymm sample)) ≤
        (((Fintype.card Ω^2+1)^L : ℕ) : ℝ)*exceptionBudget m k M κ

end Lax342547.GraphFailure
