import Lax342547.FiniteLinearLaw

/-!
---
title: Exact-image bounds for independent affine columns
type: lemma
---
Every column may have its own affine translation space, provided they
all contain one common subspace S. An injective nominal coefficient
matrix of rank t then has at least t dim(S) uniform image bits. The
estimate is valid for every t, with no bounded-rank assumption.
-/

namespace Lax342547.AffineImages

open Lax342547.MomentSpace
open scoped ENNReal

variable {J T V : Type} [Fintype J] [Fintype T]
  [AddCommGroup V] [Module Binary V]

def evaluation (S : J → Submodule Binary V) (C : Matrix J T Binary) :
    (∀ j, S j) →ₗ[Binary] (T → V) where
  toFun x t := ∑ j, C j t • (x j).val
  map_add' x y := by ext t; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext t; simp [Finset.smul_sum, smul_smul, mul_comm]

def columnMap (v : J → V) : (J → Binary) →ₗ[Binary] V where
  toFun c := ∑ j, c j • v j
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' s c := by simp [Finset.smul_sum, smul_smul]

noncomputable def law [DecidableEq J] (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (C : Matrix J T Binary) (a : J → V) : PMF (T → V) :=
  (PMF.uniformOfFintype (∀ j, S j)).map
    (fun x => (fun t => ∑ j, C j t • a j) + evaluation S C x)

axiom evaluation_rank [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) (S₀ : Submodule Binary V)
    (hS : ∀ j, S₀ ≤ S j) (C : Matrix J T Binary) (hC : Function.Injective C.mulVec) :
    Fintype.card T * Module.finrank Binary S₀ ≤
      Module.finrank Binary (LinearMap.range (evaluation S C))

axiom image_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j)
    (C : Matrix J T Binary) (hC : Function.Injective C.mulVec) (a : J → V) (y : T → V) :
    law S C a y ≤ 1 / (2 : ℝ≥0∞) ^ (Fintype.card T * Module.finrank Binary S₀)

axiom dependence_bound [DecidableEq J] [FiniteDimensional Binary V]
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | ¬ Function.Injective (columnMap (fun j => a j + (x j).val))} ≤
      (2 : ℝ≥0∞) ^ Fintype.card J / 2 ^ Module.finrank Binary S₀

axiom extension_dependence_bound {U : Type} [AddCommGroup U] [Module Binary U] [Fintype U]
    [DecidableEq J] [FiniteDimensional Binary V]
    (P : U →ₗ[Binary] V) (hP : Function.Injective P)
    (S : J → Submodule Binary V) [∀ j, Fintype (S j)]
    (S₀ : Submodule Binary V) (hS : ∀ j, S₀ ≤ S j) (a : J → V) :
    (PMF.uniformOfFintype (∀ j, S j)).toOuterMeasure
      {x | ¬ Function.Injective (fun z : U × (J → Binary) =>
        P z.1 + columnMap (fun j => a j + (x j).val) z.2)} ≤
      (Fintype.card U : ℝ≥0∞) * 2 ^ Fintype.card J / 2 ^ Module.finrank Binary S₀

end Lax342547.AffineImages
