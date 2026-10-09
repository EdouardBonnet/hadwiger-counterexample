import Lax342547.BinaryMixer
import Lax342547Proofs.Atoms
import Lax342547Proofs.OrderedMixerLaw
import Lax342547Proofs.SharpMixerLaw

namespace Lax342547Proofs.BinaryMixer

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.Atoms Lax342547.AtomDirections Lax342547.BinaryMixer

variable {k n b degree : ℕ}

theorem transpose_eval {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I Binary) (x y : I → Binary) :
    A.transpose.toBilin' x y = A.toBilin' y x := by
  simp only [Matrix.toBilin'_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.BinaryMixer.ambientParity_eval
---
Transpose reverses the point-input order. Linearity in the ambient matrix
then identifies the combined matrix with the indexed ordered parity.
-/
theorem ambientParity_eval {I F : Type} [Fintype I] [DecidableEq I] [Fintype F]
    (L : F → Matrix I I Binary) (a b : F → Binary) (E : Matrix I I Binary) (c d : Binary)
    (x y : I → Binary) :
    (ambientParity L a b E c d).toBilin' x y =
      (∑ j, (a j * (L j).toBilin' x y + b j * (L j).toBilin' y x)) +
        c * E.toBilin' x y + d * E.toBilin' y x := by
  simp only [ambientParity, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, transpose_eval]

/--
---
conclusion: Lax342547.BinaryMixer.pointInput_affine
---
At a fixed label the constant coordinate is unchanged, while each retained
base bit contributes its selector evaluation times that bit.
-/
theorem pointInput_affine (s : Fin b → Binary) {l : Tag k} {f : Flavor k}
    (p : Parameters n l f) :
    pointInput (degree := degree) s p = pointInput s (0 : Parameters n l f) +
      (directions s l f).mulVec p := by
  classical
  ext ⟨S, i⟩
  cases i with
  | none => simp [pointInput, point, baseEval, directions, Matrix.mulVec, dotProduct]
  | some i =>
    by_cases hi : i ∈ retained l f
    · simp [pointInput, point, baseEval, parameterValue, directions, Matrix.mulVec, dotProduct,
        hi, ← Subtype.ext_iff (a1 := (⟨i, hi⟩ : ParameterIndex n l f)), eq_comm]
    · have hne (j : ParameterIndex n l f) : i ≠ j.val := by
        intro h
        exact hi (h ▸ j.property)
      simp [pointInput, point, baseEval, parameterValue, directions, Matrix.mulVec, dotProduct,
        hi, hne]

theorem affine_mixed {V : Type} [AddCommGroup V] [Module Binary V]
    (B : LinearMap.BilinForm Binary V) (x y u v : V) :
    B (x + u) (y + v) + B (x + u) y + B x (y + v) + B x y = B u v := by
  simp only [map_add, LinearMap.add_apply]
  have hz (a : Binary) : a + a = 0 := ZModModule.add_self a
  calc
    _ = ((B x y + B x y) + (B x y + B x y)) +
        (B u y + B u y) + (B x v + B x v) + B u v := by abel
    _ = _ := by simp only [hz, zero_add]

theorem restriction_entry {I P Q : Type} [Fintype I] [Fintype P] [Fintype Q]
    [DecidableEq I] [DecidableEq P] [DecidableEq Q]
    (A : Matrix I I Binary) (D : Matrix I P Binary) (E : Matrix I Q Binary) (i : P) (j : Q) :
    A.toBilin' (D.mulVec (Pi.single i 1)) (E.mulVec (Pi.single j 1)) =
      (D.transpose * A * E) i j := by
  simp only [Matrix.toBilin'_apply, Matrix.mulVec_single, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul, MulOpposite.op_one, one_smul]
  rw [Finset.sum_comm]
  rfl

/--
---
conclusion: Lax342547.BinaryMixer.bilinearPart_eq
---
Taking the four mixed differences cancels both affine terms and the
constant term. The remaining coefficient is the matrix restricted to the
two flavor direction maps.
-/
theorem bilinearPart_eq (A : Moment k n b degree) (s t : Fin b → Binary)
    (l m : Tag k) (f g : Flavor k) :
    bilinearPart A s t l m f g = (directions s l f).transpose * A * directions t m g := by
  classical
  ext i j
  dsimp [bilinearPart, mixedMatrix]
  rw [pointInput_affine s (Pi.single i 1), pointInput_affine t (Pi.single j 1)]
  rw [affine_mixed]
  exact restriction_entry A _ _ i j

theorem directions_submatrix (s : Fin b → Binary) (l : Tag k) (f : Flavor k)
    (c : Fin n → Base k n) (hc : ∀ i, c i ∈ retained l f) :
    (directions (degree := degree) s l f).submatrix id (fun i => ⟨c i, hc i⟩) =
      blockDirections s c := rfl

/--
---
conclusion: Lax342547.BinaryMixer.block_rank_le
---
The chosen retained block is a submatrix of the actual mixed coefficient
matrix. Taking a submatrix cannot increase rank.
-/
theorem block_rank_le (A : Moment k n b degree) (s t : Fin b → Binary)
    (l m : Tag k) (f g : Flavor k) (c : Fin n → Base k n)
    (hc : ∀ i, c i ∈ retained l f) (hd : ∀ i, c i ∈ retained m g) :
    ((blockDirections s c).transpose * A * blockDirections t c).rank ≤
      (bilinearPart A s t l m f g).rank := by
  classical
  rw [bilinearPart_eq]
  have heq : ((directions (degree := degree) s l f).transpose * A * directions t m g).submatrix
      (fun i => ⟨c i, hc i⟩) (fun i => ⟨c i, hd i⟩) =
      (blockDirections s c).transpose * A * blockDirections t c := by
    ext i j
    rfl
  rw [← heq]
  exact Matrix.rank_submatrix_le _ _ _

theorem restrict_transpose {I P Q : Type} [Fintype I]
    (A : Matrix I I Binary) (D : Matrix I P Binary) (E : Matrix I Q Binary) :
    D.transpose * A.transpose * E = (E.transpose * A * D).transpose := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

/--
---
conclusion: Lax342547.BinaryMixer.parity_free_block
---
Restricting an ordered evaluation or its reverse gives the two ordered
blocks. Both orders of the self-Gram form vanish on the free directions.
-/
theorem parity_free_block {r : ℕ} {F : Type} [Fintype F]
    (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (L : F → Moment k n b degree) (a b' : F → Binary)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (c d : Binary) (s t : Fin b → Binary) :
    (blockDirections s free).transpose * ambientParity L a b' (selfGram hr hd M) c d *
      blockDirections t free =
        Lax342547.OrderedMixerLaw.familyParity (blockDirections s free) (blockDirections t free) a b' L := by
  simp only [ambientParity, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Lax342547.OrderedMixerLaw.familyParity, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Lax342547.OrderedMixerLaw.parity,
    Lax342547.OrderedMixerLaw.orders, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [restrict_transpose, SharpMixerLaw.selfGram_free_block, Matrix.transpose_zero,
    smul_zero, add_zero]

/--
---
conclusion: Lax342547.BinaryMixer.selfGram_parity_sharp_block
---
The two sharp restrictions are the label-weighted matrix and its
transpose. Hence all three nonzero self-Gram parities are retained as
submatrices on every pair of flavors.
-/
theorem selfGram_parity_sharp_block {r : ℕ} (hr : 2 * r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (c d : Binary) (s t : Fin b → Binary) :
    (blockDirections (k := k) s sharp).transpose *
      (c • selfGram hr hd M + d • (selfGram hr hd M).transpose) * blockDirections t sharp =
      c • Lax342547.SharpMixerLaw.weighted (fun a => s a + t a) M +
        d • (Lax342547.SharpMixerLaw.weighted (fun a => s a + t a) M).transpose := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    restrict_transpose, SharpMixerLaw.selfGram_sharp_block]
  simp only [add_comm]

end Lax342547Proofs.BinaryMixer
