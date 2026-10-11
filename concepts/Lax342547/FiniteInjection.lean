import Lax342547.SequentialTests
import Lax342547.IndependentSampling
import Lax342547.AmplifiedTests
import Lax342547.UniversalWitnesses
import Lax342547.IndependentWitnesses
import Lax342547.FiniteSampling
import Mathlib.LinearAlgebra.DFinsupp

/-!
---
title: Finite pin-injection exception
type: definition and theorem
---
Greedy independent failure probes, adaptive protected witnesses, and actual finite Fubini give an exception bound for whole-unit channel injection.
-/

namespace Lax342547.FiniteInjection

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

def pinFailure {N H : Type} [Fintype N] (V : Submodule Binary (N → Binary))
    (Y : Matrix N H Binary) (S : Submodule Binary (H → Binary)) : Prop :=
  ∃ v : V,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S

axiom finite_injection_exception {A B N H : Type}
    [Fintype A] [Fintype B] [Fintype N] [Fintype H] [DecidableEq N] [DecidableEq H]
    (α : A → ℝ) (β : B → ℝ) (V : A → Submodule Binary (N → Binary))
    (Y : B → Matrix N H Binary) (S : B → Submodule Binary (H → Binary))
    (K ℓ : ℕ) (L η δ : ℝ) (hα : Probability α) (hβ : Probability β)
    (hL : 0 ≤ L) (hgap : δ < η) (hV : ∀ a,Module.finrank Binary (V a) ≤ K)
    (hS : ∀ b,Module.finrank Binary (S b) ≤ K)
    (hcap : ∀ y,push β Y y ≤ L*weights (PMF.uniformOfFintype (Matrix N H Binary)) y)
    (havoid : ∀ j,j < ℓ → ∀ t : Fin j → A,
      cellMass α (fun a => ¬ Disjoint (V a) (⨆ i : Fin j,V (t i))) ≤ δ) :
    cellMass β (fun b => η ≤ cellMass α (fun a => pinFailure (V a) (Y b) (S b))) ≤
      (L*((2 : ℝ)^(Fintype.card H*K+2*K*ℓ)/(2 : ℝ)^(Fintype.card H*ℓ)))/(η-δ)^ℓ

end Lax342547.FiniteInjection
