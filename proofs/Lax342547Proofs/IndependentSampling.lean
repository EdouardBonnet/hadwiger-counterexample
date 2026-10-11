import Lax342547.IndependentSampling
import Lax342547Proofs.SequentialTests
import Lax342547Proofs.GreedySpaces
import Lax342547Proofs.FiniteSampling
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Fin.Tuple.Basic

namespace Lax342547Proofs.IndependentSampling
open Lax342547.IndependentSampling

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

/--
---
conclusion: Lax342547.IndependentSampling.accepted_spaces_independent
---
-/
theorem accepted_spaces_independent {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    (U : Ω → Submodule K V) (F : Ω → Prop) (n : ℕ) (s : Fin n → Ω)
    (hs : Lax342547.SequentialTests.accepts
      (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n s) :
    iSupIndep (fun i => U (s i)) := by
  induction n with
  | zero => exact iSupIndep_subsingleton _
  | succ n ih =>
    change Lax342547.SequentialTests.accepts
      (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n (Fin.init s) ∧
      (F (s (Fin.last n)) ∧ Disjoint (U (s (Fin.last n)))
        (⨆ i : Fin n,U (Fin.init s i))) at hs
    have hi := ih (Fin.init s) hs.1
    have hh := Lax342547Proofs.GreedySpaces.independent_snoc (fun i => U (Fin.init s i))
      (U (s (Fin.last n))) hi hs.2.2
    have he : (fun i : Fin (n+1) => U (s i)) =
        Fin.snoc (fun i : Fin n => U (Fin.init s i)) (U (s (Fin.last n))) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.snoc_castSucc];rfl
    rw [he]
    exact hh

/--
---
conclusion: Lax342547.IndependentSampling.greedy_failure_lower_probability
---
-/
theorem greedy_failure_lower_probability {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Fintype Ω] (U : Ω → Submodule K V) (μ : Ω → ℝ) (F : Ω → Prop)
    (η δ : ℝ) (n : ℕ) (hμ : Probability μ) (hgap : δ ≤ η)
    (hF : η ≤ cellMass μ F)
    (havoid : ∀ j,j < n → ∀ t : Fin j → Ω,
      cellMass μ (fun x => ¬ Disjoint (U x) (⨆ i : Fin j,U (t i))) ≤ δ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (fun s => Lax342547.SequentialTests.accepts
        (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n s) := by
  exact Lax342547Proofs.SequentialTests.bounded_sequential_failure_lower μ F
    (fun j t x => Disjoint (U x) (⨆ i : Fin j,U (t i))) η δ hμ hgap hF n
    (fun j hj t _ => havoid j hj t)

end Lax342547Proofs.IndependentSampling
