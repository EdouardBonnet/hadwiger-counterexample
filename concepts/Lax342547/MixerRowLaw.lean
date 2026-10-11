import Lax342547.MixerCompatibility
import Lax342547.FiniteLinearLaw

/-!
---
title: The distribution of mixer rows on free directions
type: lemma
---
For a uniform matrix L, the joint observations ZᵀLD and DᵀLW have
density at most 2^(rank(Z) rank(W)) relative to the completely uniform
list, when Z,W,D have independent columns. This is the single-matrix
domination bound in the proof of Lemma 5.5.
-/

namespace Lax342547.MixerRowLaw

variable {K I E F N : Type} [Field K] [Fintype I]

def directions (D : Matrix I N K) :
    (Matrix E I K × Matrix I F K) →ₗ[K] (Matrix E N K × Matrix N F K) where
  toFun p := (p.1 * D, D.transpose * p.2)
  map_add' x y := by simp [Matrix.add_mul, Matrix.mul_add]
  map_smul' c x := by simp [Matrix.smul_mul, Matrix.mul_smul]

def observations (Z : Matrix I E K) (W : Matrix I F K) (D : Matrix I N K) :
    Matrix I I K →ₗ[K] (Matrix E N K × Matrix N F K) :=
  (directions D).comp (MixerCompatibility.restrictions Z W)

open Lax342547.MomentSpace
open scoped ENNReal

axiom row_law_bound {I E F N : Type} [Fintype I] [Fintype E] [Fintype F] [Fintype N]
    [DecidableEq I] [DecidableEq E] [DecidableEq F] [DecidableEq N]
    (Z : Matrix I E Binary) (W : Matrix I F Binary) (D : Matrix I N Binary)
    (hZ : Function.Injective Z.mulVec) (hW : Function.Injective W.mulVec) (hD : Function.Injective D.mulVec)
    (y : Matrix E N Binary × Matrix N F Binary) :
    (PMF.uniformOfFintype (Matrix I I Binary)).map (observations Z W D) y ≤
      2 ^ (Fintype.card E * Fintype.card F) * PMF.uniformOfFintype (Matrix E N Binary × Matrix N F Binary) y

end Lax342547.MixerRowLaw
