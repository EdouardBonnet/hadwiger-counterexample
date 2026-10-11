import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Recovery of low-rank Boolean moments from low degrees
type: lemma
---
The rank obstruction in the second half of Lemma 5.2. A first nonzero
selector moment of degree d produces an identity submatrix of size
binomial(d, floor(d/2)). Consequently a Boolean moment matrix of rank at
most r vanishes if all its moments of degree at most r vanish.
-/

namespace Lax342547.MomentRecovery

open Lax342547.MomentSpace

def IsSelectorHankel {Base : Type} {b degree : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary) : Prop :=
  ∀ (S T U V : SelectorCoordinates b degree) (i j : Base),
    S.val ∪ T.val = U.val ∪ V.val → w (S, i) (T, j) = w (U, i) (V, j)

axiom eq_zero_of_rank_le {Base : Type} [Fintype Base] {b degree r : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary)
    (hH : IsSelectorHankel w) (hrank : w.rank ≤ r)
    (hlow : ∀ (S T : SelectorCoordinates b degree) (i j : Base),
      (S.val ∪ T.val).card ≤ r → w (S, i) (T, j) = 0) : w = 0

axiom eq_of_agree_low {Base : Type} [Fintype Base] {b degree r₁ r₂ : ℕ}
    (w v : Matrix (SelectorCoordinates b degree × Base)
      (SelectorCoordinates b degree × Base) Binary)
    (hw : IsSelectorHankel w) (hv : IsSelectorHankel v)
    (hrw : w.rank ≤ r₁) (hrv : v.rank ≤ r₂)
    (hlow : ∀ (S T : SelectorCoordinates b degree) (i j : Base),
      (S.val ∪ T.val).card ≤ r₁ + r₂ → w (S, i) (T, j) = v (S, i) (T, j)) : w = v

end Lax342547.MomentRecovery
