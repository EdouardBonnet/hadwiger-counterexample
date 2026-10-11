import Lax342547.AffineSliceVariance

/-!
---
title: Uniform quantitative thresholds for affine-slice variance
type: lemma
---
The variance budget is bounded by a fixed constant times 2^(-floor(n/2))
whenever the ambient dimension is at least n. One threshold supplies every
Gram comparison margin and any requested positive error, before choosing
coefficient laws, prescribed Grams, or common tests.
-/

namespace Lax342547.AffineSliceScales
noncomputable section
open Lax342547.RawFrameComparison

def budget (S D : Type) [Fintype S] [Fintype D] (N n : ℕ) (β : ℝ) : ℝ :=
    (Fintype.card S : ℝ)*errorBound N (Option D) (Option D) (Option D) (Option D)+
      4*(((2 : ℝ)^(2*Fintype.card D+1)/(2 : ℝ)^n)/β^2)

def scale (S D : Type) [Fintype S] [Fintype D] (β : ℝ) : ℝ :=
    (Fintype.card S : ℝ)*Lax342547.RawFrameComparison.scale (Option D) (Option D) (Option D) (Option D)+
      4*((2 : ℝ)^(2*Fintype.card D+1)/β^2)

axiom budget_decay (S D : Type) [Fintype S] [Fintype D] (N n : ℕ) (β : ℝ) (hn : n ≤ N) :
    budget S D N n β ≤ scale S D β/(2 : ℝ)^(n/2)

axiom uniform_threshold (S D : Type) [Fintype S] [Fintype D] (β ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ,∀ n ≥ n₀,∀ N ≥ n,
      Fintype.card (Option D)+Fintype.card (Option D)+1 ≤ N ∧
      ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))*
          ((2 : ℝ)^(Fintype.card (Option D)*Fintype.card (Option D)+2))/Real.sqrt ((2 : ℝ)^N) ≤
        1/(2 : ℝ)^(Fintype.card (Lax342547.CrossGramBasis.Slots (Option D) (Option D) (Option D) (Option D))+1) ∧
      budget S D N n β ≤ ε

end
end Lax342547.AffineSliceScales
