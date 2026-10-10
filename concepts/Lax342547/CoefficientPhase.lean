import Lax342547.TargetMatrices
import Lax342547.GramTests

/-!
---
title: Coefficient phases as dot products of rank-factor images
type: definition and theorem
---
A binary coefficient tensor contracted with a cross Gram matrix is the dot product of its two rank-factor image tuples, flattened over rank positions and ambient coordinates.
-/

namespace Lax342547.CoefficientPhase

open Lax342547.MomentSpace Lax342547.Walsh

noncomputable def coefficientPair {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (C : Matrix I J Binary) (X : Matrix N I Binary) (Y : Matrix N J Binary) : Binary :=
  ∑ i, ∑ j, C i j * (X.transpose * Y) i j

noncomputable def factorImage {I R N : Type} [Fintype I]
    (A : Matrix I R Binary) (X : Matrix N I Binary) : R × N → Binary :=
  fun rn => (X * A) rn.2 rn.1

axiom coefficient_trace {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    (C : Matrix I J Binary) (X : Matrix N I Binary) (Y : Matrix N J Binary) :
    coefficientPair C X Y = Matrix.trace (C.transpose * (X.transpose * Y))

axiom independent_factor_phase {I J R N : Type}
    [Fintype I] [Fintype J] [Fintype R] [Fintype N]
    (A : Matrix I R Binary) (B : Matrix J R Binary) (X : Matrix N I Binary) (Y : Matrix N J Binary) :
    coefficientPair (A * B.transpose) X Y = dotProduct (factorImage A X) (factorImage B Y)

end Lax342547.CoefficientPhase
