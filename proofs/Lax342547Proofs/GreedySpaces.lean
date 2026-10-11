import Lax342547.GreedySpaces
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Fin.Tuple.Basic

namespace Lax342547Proofs.GreedySpaces
open Lax342547.GreedySpaces

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace
open scoped BigOperators

/--
---
conclusion: Lax342547.GreedySpaces.independent_snoc
---
-/
theorem independent_snoc {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (U : Fin n → Submodule K V) (W : Submodule K V)
    (hU : iSupIndep U) (hW : Disjoint W (⨆ i,U i)) : iSupIndep (Fin.snoc U W) := by
  classical
  let S := Finset.univ.map (Fin.castSuccEmb : Fin n ↪ Fin (n+1))
  let f : Fin (n+1) → Submodule K V := Fin.snoc U W
  have hs : S.SupIndep f := by
    rw [Finset.supIndep_map]
    simpa only [f,Function.comp_def,Fin.coe_castSuccEmb,Fin.snoc_castSucc] using hU.sup_indep_univ
  have hd : Disjoint (f (Fin.last n)) (S.sup f) := by
    have hl : f (Fin.last n) = W := by simp only [f,Fin.snoc_last]
    rw [hl]
    have he : S.sup f = ⨆ i : Fin n,U i := by
      dsimp only [S]
      rw [Finset.sup_map]
      simp only [f,Fin.coe_castSuccEmb,Function.comp_def,Fin.snoc_castSucc,Finset.sup_eq_iSup,Finset.mem_univ,iSup_true]
    rw [he]
    exact hW
  have hh := hs.insert hd
  have hu : (Finset.univ : Finset (Fin (n+1))) = insert (Fin.last n) S := by
    ext i
    simp only [Finset.mem_univ,true_iff]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩
  rw [← hu] at hh
  exact hh.iSupIndep_of_univ

/--
---
conclusion: Lax342547.GreedySpaces.finite_span_dimension
---
-/
theorem finite_span_dimension {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : ι → Submodule K V) (S : Finset ι) :
    Module.finrank K ↥(S.sup U) ≤ ∑ i ∈ S,Module.finrank K (U i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (U i) (S.sup U)
    omega

/--
---
conclusion: Lax342547.GreedySpaces.accumulated_dimension
---
-/
theorem accumulated_dimension {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Ω → Submodule K V) (r n : ℕ) (s : Fin n → Ω)
    (hU : ∀ x,Module.finrank K (U x) ≤ r) :
    Module.finrank K ↥(⨆ i : Fin n,U (s i)) ≤ r*n := by
  have hh := Lax342547.GreedySpaces.finite_span_dimension (fun i : Fin n => U (s i)) Finset.univ
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hU (s i))
  have hm := hh.trans hs
  have hspan : Finset.univ.sup (fun i : Fin n => U (s i)) = ⨆ i : Fin n,U (s i) := by
    rw [Finset.sup_eq_iSup]
    simp
  have he := congrArg (fun W : Submodule K V => Module.finrank K W) hspan
  rw [← he]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using hm

end Lax342547Proofs.GreedySpaces
