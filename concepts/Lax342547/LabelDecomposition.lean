import Lax342547.BaseMoments
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Low-rank Boolean moments have bounded label support
type: lemma
---
Lemma 5.2, with the sufficient selector-degree hypothesis used in its proof.
Every rank-at-most-R moment matrix splits over at most R labels. The base
blocks obey the binary moment identities and their ranks sum to at most R.
-/

namespace Lax342547.LabelDecomposition

open Lax342547.MomentSpace Lax342547.BaseMoments

axiom low_rank_label_decomposition {Base : Type} [Fintype Base] {b degree R : ℕ}
    (w : Matrix (SelectorCoordinates b degree × Option Base)
      (SelectorCoordinates b degree × Option Base) Binary)
    (hw : w ∈ momentSpace (selectorEval (degree := degree)) Set.univ)
    (hrank : w.rank ≤ R) (hdegree : 6 * R + 4 ≤ degree) :
    ∃ L : Finset (Fin b → Binary),
    ∃ Z : (Fin b → Binary) → Matrix (Option Base) (Option Base) Binary,
      L.card ≤ R ∧ (∀ s ∈ L, IsBaseMoment (Z s)) ∧
      (∑ s ∈ L, (Z s).rank) ≤ R ∧
      ∀ i k, w i k = ∑ s ∈ L, selectorEval s i.1 * selectorEval s k.1 * Z s i.2 k.2

end Lax342547.LabelDecomposition
