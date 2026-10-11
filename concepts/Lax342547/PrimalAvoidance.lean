import Lax342547.FiniteLinearLaw
import Lax342547.ChannelColumns
import Lax342547.InjectiveFrames
import Lax342547.PhaseAverages

/-!
---
title: Uniform primal-span avoidance
type: definition and theorem
---
Exact random matrix vector laws and finite subspace counts bound intersections of the complete primal image with a fixed space.
-/

namespace Lax342547.PrimalAvoidance

open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators ENNReal

noncomputable def evalMatrix {B N : Type} [Fintype B] (c : B → Binary) :
    Matrix N B Binary →ₗ[Binary] (N → Binary) where
  toFun A := A.mulVec c
  map_add' A D := Matrix.add_mulVec A D c
  map_smul' a A := by simp [Matrix.smul_mulVec]

axiom evalMatrix_surjective {B N : Type} [Fintype B] [DecidableEq B]
    (c : B → Binary) (hc : c ≠ 0) : Function.Surjective (evalMatrix (N := N) c)

axiom matrix_vector_uniform {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (c : B → Binary) (hc : c ≠ 0) :
    (PMF.uniformOfFintype (Matrix N B Binary)).map (fun A : Matrix N B Binary => A.mulVec c) =
      PMF.uniformOfFintype (N → Binary)

axiom uniform_subspace_mass {N : Type} [Fintype N] [DecidableEq N] (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (N → Binary))) (fun v => v ∈ W) =
      (2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N

axiom fixed_vector_subspace_mass {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (c : B → Binary) (hc : c ≠ 0) (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N B Binary))) (fun A => A.mulVec c ∈ W) =
      (2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N

axiom matrix_span_hit_mass {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N B Binary)))
      (fun A => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W) ≤
      (2 : ℝ)^(Fintype.card B+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N

axiom capped_matrix_span_hit {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (μ : Matrix N B Binary → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ A,μ A ≤ L*weights (PMF.uniformOfFintype (Matrix N B Binary)) A)
    (W : Submodule Binary (N → Binary)) :
    cellMass μ (fun A => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W) ≤
      L*((2 : ℝ)^(Fintype.card B+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N)

end Lax342547.PrimalAvoidance
