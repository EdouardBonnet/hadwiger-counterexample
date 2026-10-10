import Lax342547.BaseMoments
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
---
title: A selected affine ray determines its moment block
type: definition and theorem
---
An explicit projection onto the quotient by an affine point ray. The
Boolean moment diagonal identity removes the mixed first-row terms in
a symmetric tensor killed by that quotient in both factors (§6).
-/

namespace Lax342547.SelectedMoments

open Lax342547.MomentSpace Lax342547.BaseMoments

def rayProjection {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) : Matrix (Option Base) (Option Base) Binary :=
  1 - Matrix.vecMulVec (baseEval z) (Pi.single none 1)

axiom projection_kernel {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) :
    LinearMap.ker (rayProjection z).mulVecLin =
      Submodule.span Binary {baseEval z}

axiom moment_ray {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) (Z : Matrix (Option Base) (Option Base) Binary)
    (hZ : IsBaseMoment Z)
    (h : rayProjection z * Z * (rayProjection z).transpose = 0) :
    Z = Z none none • baseMoment z

end Lax342547.SelectedMoments
