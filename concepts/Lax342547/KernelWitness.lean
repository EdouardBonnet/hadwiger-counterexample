import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
---
title: Bounded descriptions of large matrix kernels
type: theorem
---
A large sum of kernel dimensions has a certificate using a bounded
number of coefficient columns per component. Enumerating these matrices
costs only an exponential in their coefficient dimensions.
-/

namespace Lax342547.KernelWitness

open Lax342547.MomentSpace
open scoped ENNReal

axiom exists_kernel_witness {I N : Type} [Fintype I] [Fintype N]
    (A : Matrix N I Binary) (q : ℕ) :
    ∃ C : Matrix I (Fin q) Binary, A * C = 0 ∧
      min q (Module.finrank Binary (LinearMap.ker A.mulVecLin)) ≤ C.rank

axiom exists_family_witness {Comp I N : Type} [Fintype Comp] [Fintype I] [Fintype N]
    (A : Comp → Matrix N I Binary) (q : ℕ)
    (hq : q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A e).mulVecLin)) :
    ∃ C : Comp → Matrix I (Fin q) Binary, (∀ e, A e * C e = 0) ∧ q ≤ ∑ e, (C e).rank

axiom coefficient_count {Comp I : Type} [Fintype Comp] [Fintype I] (q : ℕ) :
    Nat.card (Comp → Matrix I (Fin q) Binary) = 2 ^ (Fintype.card Comp * Fintype.card I * q)

axiom kernel_event_bound {Ω Comp I N : Type}
    [Fintype Ω] [Fintype Comp] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Comp → Matrix N I Binary) (q : ℕ) (cap : ℝ≥0∞)
    (hcap : ∀ C : Comp → Matrix I (Fin q) Binary, q ≤ (∑ e, (C e).rank) →
      p.toOuterMeasure {o | ∀ e, A o e * C e = 0} ≤ cap) :
    p.toOuterMeasure {o | q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A o e).mulVecLin)} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * Fintype.card I * q) * cap

end Lax342547.KernelWitness
