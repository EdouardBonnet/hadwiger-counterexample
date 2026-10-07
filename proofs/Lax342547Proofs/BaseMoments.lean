import Lax342547.BaseMoments
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.BaseMoments

open Lax342547.MomentSpace Lax342547.BaseMoments

variable {Base : Type}

theorem binary_mul_self (x : Binary) : x * x = x := by fin_cases x <;> rfl

theorem baseMoment_properties (z : Base → Binary) : IsBaseMoment (baseMoment z) := by
  constructor
  · intro i j; exact mul_comm _ _
  · intro i; simp [baseMoment, baseEval, binary_mul_self]

theorem properties_of_mem {Z : Matrix (Option Base) (Option Base) Binary}
    (hZ : Z ∈ baseMomentSpace Base) : IsBaseMoment Z := by
  induction hZ using Submodule.span_induction with
  | mem Z hZ => obtain ⟨z, rfl⟩ := hZ; exact baseMoment_properties z
  | zero => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | add Z W _ _ hZ hW =>
    exact ⟨fun i j => congrArg₂ (· + ·) (hZ.1 i j) (hW.1 i j),
      fun i => congrArg₂ (· + ·) (hZ.2 i) (hW.2 i)⟩
  | smul c Z _ hZ =>
    exact ⟨fun i j => congrArg (c * ·) (hZ.1 i j),
      fun i => congrArg (c * ·) (hZ.2 i)⟩

theorem baseMoment_mem (z : Base → Binary) : baseMoment z ∈ baseMomentSpace Base :=
  Submodule.subset_span ⟨z, rfl⟩

section BasisMatrices

variable [DecidableEq Base]

def diagonalAtom (b : Base) : Matrix (Option Base) (Option Base) Binary :=
  Matrix.single none (some b) 1 + Matrix.single (some b) none 1 + Matrix.single (some b) (some b) 1

def offDiagonalAtom (b c : Base) : Matrix (Option Base) (Option Base) Binary :=
  Matrix.single (some b) (some c) 1 + Matrix.single (some c) (some b) 1

theorem zero_moment : baseMoment (0 : Base → Binary) = Matrix.single none none 1 := by
  ext (_ | i) (_ | j) <;> simp [baseMoment, baseEval]

theorem diagonalAtom_eq (b : Base) :
    diagonalAtom b = baseMoment (0 : Base → Binary) + baseMoment (Pi.single b 1) := by
  ext (_ | i) (_ | j)
  · simp [diagonalAtom, baseMoment, baseEval, ZModModule.add_self]
  · by_cases h : b = j <;> simp [diagonalAtom, baseMoment, baseEval, h]
  · by_cases h : b = i <;> simp [diagonalAtom, baseMoment, baseEval, h]
  · by_cases hi : b = i <;> by_cases hj : b = j <;>
      simp_all [diagonalAtom, baseMoment, baseEval]

theorem offDiagonalAtom_eq (b c : Base) :
    offDiagonalAtom b c = baseMoment (0 : Base → Binary) + baseMoment (Pi.single b 1) +
      baseMoment (Pi.single c 1) + baseMoment (Pi.single b 1 + Pi.single c 1) := by
  ext (_ | i) (_ | j)
  · simp [offDiagonalAtom, baseMoment, baseEval, ZModModule.add_self]
  · simp [offDiagonalAtom, baseMoment, baseEval, ZModModule.add_self]
  · simp [offDiagonalAtom, baseMoment, baseEval, ZModModule.add_self]
  · by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      by_cases hci : c = i <;> by_cases hcj : c = j <;>
      simp_all [offDiagonalAtom, baseMoment, baseEval, ZModModule.add_self]

theorem constant_mem : (Matrix.single none none (1 : Binary) : Matrix (Option Base) (Option Base) Binary)
    ∈ baseMomentSpace Base := by rw [← zero_moment]; exact baseMoment_mem _

theorem diagonalAtom_mem (b : Base) : diagonalAtom b ∈ baseMomentSpace Base := by
  rw [diagonalAtom_eq]
  exact (baseMomentSpace Base).add_mem (baseMoment_mem _) (baseMoment_mem _)

theorem offDiagonalAtom_mem (b c : Base) : offDiagonalAtom b c ∈ baseMomentSpace Base := by
  rw [offDiagonalAtom_eq]
  exact (baseMomentSpace Base).add_mem
    ((baseMomentSpace Base).add_mem
      ((baseMomentSpace Base).add_mem (baseMoment_mem _) (baseMoment_mem _)) (baseMoment_mem _))
    (baseMoment_mem _)

end BasisMatrices

theorem base_expansion [Fintype Base] [LinearOrder Base]
    (Z : Matrix (Option Base) (Option Base) Binary) (hZ : IsBaseMoment Z) :
    Z = Z none none • Matrix.single none none 1 +
      (∑ b, Z none (some b) • diagonalAtom b) +
      ∑ b, ∑ c, (if b < c then Z (some b) (some c) else 0) • offDiagonalAtom b c := by
  ext (_ | i) (_ | j) <;>
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [diagonalAtom, offDiagonalAtom]
  · simp [diagonalAtom, offDiagonalAtom,
      Matrix.single_apply, mul_ite]
  · simpa [diagonalAtom, offDiagonalAtom,
      Matrix.single_apply, smul_eq_mul, ite_and, mul_ite] using hZ.1 (some i) none
  · have hd := hZ.2 (some i)
    have hs := hZ.1 (some i) (some j)
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [diagonalAtom, offDiagonalAtom,
        Matrix.single_apply, ite_and, mul_add, mul_ite, Finset.sum_add_distrib,
        hij, ne_of_lt hij, not_lt_of_ge (le_of_lt hij)]
    · subst j
      simpa [diagonalAtom, offDiagonalAtom,
        Matrix.single_apply, smul_eq_mul, ite_and, mul_add, mul_ite, Finset.sum_add_distrib]
        using hd
    · simpa [diagonalAtom, offDiagonalAtom,
        Matrix.single_apply, smul_eq_mul, ite_and, mul_add, mul_ite, Finset.sum_add_distrib,
        hij, ne_of_lt hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)] using hs

/--
---
conclusion: Lax342547.BaseMoments.mem_baseMomentSpace_iff
---
Point moments satisfy symmetry and the binary diagonal identity. Conversely,
expand a matrix in the constant, diagonal, and symmetric off-diagonal
generators. Each generator is a sum of at most four point moments.
-/
theorem mem_baseMomentSpace_iff [Fintype Base]
    (Z : Matrix (Option Base) (Option Base) Binary) :
    Z ∈ baseMomentSpace Base ↔ IsBaseMoment Z := by
  classical
  constructor
  · exact properties_of_mem
  · intro hZ
    let : LinearOrder Base := LinearOrder.lift' (Fintype.equivFin Base)
      (Fintype.equivFin Base).injective
    rw [base_expansion Z hZ]
    apply (baseMomentSpace Base).add_mem
    · exact (baseMomentSpace Base).add_mem
        ((baseMomentSpace Base).smul_mem _ constant_mem)
        ((baseMomentSpace Base).sum_mem (fun b _ =>
          (baseMomentSpace Base).smul_mem _ (diagonalAtom_mem b)))
    · apply (baseMomentSpace Base).sum_mem
      intro b _
      exact (baseMomentSpace Base).sum_mem (fun c _ =>
        (baseMomentSpace Base).smul_mem _ (offDiagonalAtom_mem b c))

end Lax342547Proofs.BaseMoments
