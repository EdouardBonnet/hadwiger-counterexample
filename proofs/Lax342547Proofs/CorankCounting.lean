import Lax342547.CorankCounting
import Lax342547Proofs.MixerCompatibility
import Lax342547Proofs.FiniteLinearLaw
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.CorankCounting

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CorankCounting.exists_row_relations
---
Select s basis vectors of the kernel of Mᵀ. They are independent rows
of the relation matrix C. A left inverse of Cᵀ proves C is surjective.
-/
theorem exists_row_relations {K I J : Type} [Field K] [Fintype I] [Fintype J]
    (M : Matrix I J K) (s : ℕ) (hs : M.rank + s ≤ Fintype.card I) :
    ∃ C : Matrix (Fin s) I K, Function.Surjective C.mulVec ∧ C * M = 0 := by
  classical
  let S := LinearMap.ker M.transpose.mulVecLin
  have hd := M.transpose.mulVecLin.finrank_range_add_finrank_ker
  change M.transpose.rank + Module.finrank K S = Module.finrank K (I → K) at hd
  rw [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card] at hd
  have hdim : s ≤ Module.finrank K S := by omega
  let b := Module.finBasis K S
  let C : Matrix (Fin s) I K := fun a i => (b (Fin.castLE hdim a)).val i
  have hCt : Function.Injective C.transpose.mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    exact (b.linearIndependent.comp (Fin.castLE hdim) (Fin.castLE_injective hdim)).map'
      S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse C.transpose hCt
  have hCU : C * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  refine ⟨C, ?_, ?_⟩
  · intro y
    refine ⟨U.transpose.mulVec y, ?_⟩
    rw [Matrix.mulVec_mulVec, hCU, Matrix.one_mulVec]
  · ext a j
    have h : M.transpose.mulVec (b (Fin.castLE hdim a)).val = 0 :=
      (b (Fin.castLE hdim a)).property
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, C, Matrix.transpose_apply,
      Matrix.zero_apply, Pi.zero_apply, mul_comm] using congrFun h j

open Lax342547.MomentSpace
open scoped ENNReal

theorem card_annihilated {I J : Type} [Fintype I] [Fintype J] (s : ℕ)
    (C : Matrix (Fin s) I Binary) (hC : Function.Surjective C.mulVec) :
    Nat.card {M : Matrix I J Binary // C * M = 0} ≤
      2 ^ ((Fintype.card I - s) * Fintype.card J) := by
  classical
  let S := LinearMap.ker C.mulVecLin
  have hd := C.mulVecLin.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hC, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
  change s + Module.finrank Binary S = Fintype.card I at hd
  have hdim : Module.finrank Binary S = Fintype.card I - s := by omega
  let g : {M : Matrix I J Binary // C * M = 0} → (J → S) := fun M j =>
    ⟨fun i => M.val i j, by
      change C.mulVec (fun i => M.val i j) = 0
      ext a
      change (C * M.val) a j = 0
      rw [M.property]
      rfl⟩
  have hg : Function.Injective g := by
    intro M N he
    apply Subtype.ext
    ext i j
    exact congrFun (congrArg Subtype.val (congrFun he j)) i
  calc
    _ = Fintype.card {M : Matrix I J Binary // C * M = 0} := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (J → S) := Fintype.card_le_of_injective g hg
    _ = _ := by rw [Fintype.card_fun, FiniteLinearLaw.binary_card S, hdim, pow_mul]

/--
---
conclusion: Lax342547.CorankCounting.card_corank
---
Choose independent row relations for each bad matrix, and partition by
that choice. There are at most 2^(sm) relation matrices. Each fiber has
at most 2^((m-s)n) matrices because all n columns lie in a kernel of
dimension m-s.
-/
theorem card_corank {I J : Type} [Fintype I] [Fintype J] (s : ℕ) :
    Nat.card {M : Matrix I J Binary // M.rank + s ≤ Fintype.card I} ≤
      2 ^ (s * Fintype.card I + (Fintype.card I - s) * Fintype.card J) := by
  classical
  let T := {M : Matrix I J Binary // M.rank + s ≤ Fintype.card I}
  let Q := {C : Matrix (Fin s) I Binary // Function.Surjective C.mulVec}
  have he (M : T) := Lax342547.CorankCounting.exists_row_relations M.val s M.property
  choose C hC hCM using he
  let q : T → Q := fun M => ⟨C M, hC M⟩
  have hf (A : Q) : Fintype.card {M : T // q M = A} ≤
      2 ^ ((Fintype.card I - s) * Fintype.card J) := by
    let f : {M : T // q M = A} → {M : Matrix I J Binary // A.val * M = 0} :=
      fun M => ⟨M.val.val, by
        have h : C M.val = A.val := congrArg Subtype.val M.property
        rw [← h]
        exact hCM M.val⟩
    have hi : Function.Injective f := by
      intro M N h
      have h' : M.val.val = N.val.val := by simpa only [f, Subtype.mk.injEq] using h
      exact Subtype.ext (Subtype.ext h')
    exact (Fintype.card_le_of_injective f hi).trans
      (by simpa only [Nat.card_eq_fintype_card] using card_annihilated (J := J) s A.val A.property)
  have h := Finset.card_le_mul_card_image_of_maps_to
    (f := q) (s := Finset.univ) (t := Finset.univ) (by simp)
    (2 ^ ((Fintype.card I - s) * Fintype.card J)) (fun A _ => by
      simpa only [Fintype.card_subtype] using hf A)
  have hQ : Fintype.card Q ≤ 2 ^ (s * Fintype.card I) := by
    calc
      _ ≤ Fintype.card (Matrix (Fin s) I Binary) := Fintype.card_subtype_le _
      _ = _ := by
        change Fintype.card (Fin s → I → Binary) = _
        simp [Binary, ZMod.card, ← pow_mul, Nat.mul_comm]
  calc
    Nat.card T = Fintype.card T := Nat.card_eq_fintype_card
    _ ≤ 2 ^ ((Fintype.card I - s) * Fintype.card J) * Fintype.card Q :=
      by simpa only [Finset.card_univ] using h
    _ ≤ 2 ^ ((Fintype.card I - s) * Fintype.card J) * 2 ^ (s * Fintype.card I) :=
      Nat.mul_le_mul_left _ hQ
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem uniform_corank_bound_raw {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (s : ℕ) :
    (PMF.uniformOfFintype (Matrix I J Binary)).toOuterMeasure {M | M.rank + s ≤ Fintype.card I} ≤
      (2 : ℝ≥0∞) ^ (s * Fintype.card I + (Fintype.card I - s) * Fintype.card J) /
        2 ^ (Fintype.card I * Fintype.card J) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have h : (Fintype.card {M : Matrix I J Binary // M.rank + s ≤ Fintype.card I} : ℝ≥0∞) ≤
      2 ^ (s * Fintype.card I + (Fintype.card I - s) * Fintype.card J) := by
    exact_mod_cast (show Fintype.card {M : Matrix I J Binary // M.rank + s ≤ Fintype.card I} ≤ _ from
      by simpa only [Nat.card_eq_fintype_card] using Lax342547.CorankCounting.card_corank (I := I) (J := J) s)
  have hcard : (Fintype.card (Matrix I J Binary) : ℝ≥0∞) = 2 ^ (Fintype.card I * Fintype.card J) := by
    change (Fintype.card (I → J → Binary) : ℝ≥0∞) = _
    simp [Binary, ZMod.card, ← pow_mul, Nat.mul_comm]
  rw [hcard]
  exact ENNReal.div_le_div_right h _

/--
---
conclusion: Lax342547.CorankCounting.uniform_corank_bound
---
Normalize the independent-relation count and cancel the common power
of two, obtaining exactly 2^(sm)/2^(sn). If s exceeds the number of rows,
the bad event is empty.
-/
theorem uniform_corank_bound {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (s : ℕ) :
    (PMF.uniformOfFintype (Matrix I J Binary)).toOuterMeasure {M | M.rank + s ≤ Fintype.card I} ≤
      (2 : ℝ≥0∞) ^ (s * Fintype.card I) / 2 ^ (s * Fintype.card J) := by
  by_cases hs : s ≤ Fintype.card I
  · calc
      _ ≤ (2 : ℝ≥0∞) ^ (s * Fintype.card I + (Fintype.card I - s) * Fintype.card J) /
          2 ^ (Fintype.card I * Fintype.card J) := uniform_corank_bound_raw s
      _ = _ := by
        have he : Fintype.card I * Fintype.card J =
            s * Fintype.card J + (Fintype.card I - s) * Fintype.card J := by
          rw [← Nat.add_mul, Nat.add_sub_of_le hs]
        rw [pow_add, he, pow_add]
        exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)
  · have he : {M : Matrix I J Binary | M.rank + s ≤ Fintype.card I} = ∅ := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [he]
    simp

end Lax342547Proofs.CorankCounting
