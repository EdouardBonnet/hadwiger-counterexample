import Lax342547.RawContractions
import Lax342547.TableContractions

namespace Lax342547Proofs.RawContractions

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.ReferencePins Lax342547.RawContractions Lax342547.ConcreteGeometry

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N] {E : Matrix B B Binary}

/--
---
conclusion: Lax342547.RawContractions.observation_blocks
---
An endpoint-supported nominal primal or channel vector selects exactly
the corresponding P, Q, X, or Y block of the joint observation matrix.
-/
theorem observation_blocks (o : Fin 2 → Comp → Frame B H N E) (e : Comp) (s : Bool) (i : Fin 2)
    (v : B → Binary) (w : H → Binary) :
    observation o (e, s) (primalEmbedding i v) =
      (if s then (o i e).P.mulVec v else (o i e).Q.mulVec v) ∧
    observation o (e, s) (channelEmbedding i w) =
      (if s then (o i e).X.mulVec w else (o i e).Y.mulVec w) := by
  classical
  constructor <;> ext n <;> cases s <;> fin_cases i <;>
    simp [observation, observationMatrix, Lax342547.ProductImages.jointMatrix,
      Lax342547.FrameSymmetry.plus, Lax342547.FrameSymmetry.minus,
      primalEmbedding, channelEmbedding, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem raw_plus (oA oB : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) :
    fullPlus (rawForms oA oB) e i z = ((oB z e).Y.transpose * (oA i e).P).mulVecLin := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  change dotProduct (observation oA (e, true) (primalEmbedding i v))
    (observation oB (e, false) (channelEmbedding z (Pi.single h 1))) = _
  rw [(Lax342547.RawContractions.observation_blocks oA e true i v 0).1,
    (Lax342547.RawContractions.observation_blocks oB e false z 0 (Pi.single h 1)).2]
  simp only [Bool.false_eq_true, if_false, if_true, Matrix.mulVecLin_apply,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem raw_minus (oA oB : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2) :
    fullMinus (rawForms oA oB) e i z = ((oB z e).X.transpose * (oA i e).Q).mulVecLin := by
  classical
  apply LinearMap.ext
  intro v
  funext h
  change dotProduct (observation oB (e, true) (channelEmbedding z (Pi.single h 1)))
    (observation oA (e, false) (primalEmbedding i v)) = _
  rw [(Lax342547.RawContractions.observation_blocks oB e true z 0 (Pi.single h 1)).2,
    (Lax342547.RawContractions.observation_blocks oA e false i v 0).1]
  simp only [Bool.false_eq_true, if_false, if_true, Matrix.mulVecLin_apply,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

omit [Fintype N] in
theorem ambient_matrix (F G : Matrix H B Binary) :
    Lax342547.TensorContractions.ambient F.mulVecLin G.mulVecLin = matrixPair (F.transpose * G) := by
  classical
  unfold Lax342547.TensorContractions.ambient
  congr 1
  ext i j
  simp [LinearMap.BilinForm.toMatrix'_apply, dotProduct,
    Matrix.mul_apply, dotProductBilin]

omit [Fintype H] [Fintype N] in
theorem pair_trace (A M : Matrix B B Binary) : matrixPair A M = Matrix.trace (A.transpose * M) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    matrixPair, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    matrixEntry, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_comm

theorem channel_contraction (F G : Frame B H N E) (M : Matrix B B Binary) :
    Lax342547.TensorContractions.ambient (G.Y.transpose * F.P).mulVecLin
      (G.X.transpose * F.Q).mulVecLin M = contraction G (sandwich F.P F.Q M) := by
  rw [ambient_matrix, pair_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  change Matrix.trace ((F.Q.transpose * G.X * (G.Y.transpose * F.P)) * M) =
    Matrix.trace (G.X * G.Y.transpose * (F.P * M * F.Q.transpose))
  calc
    _ = Matrix.trace (F.Q.transpose * (G.X * G.Y.transpose * (F.P * M))) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((G.X * G.Y.transpose * (F.P * M)) * F.Q.transpose) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

/--
---
conclusion: Lax342547.RawContractions.raw_contraction
---
The two channel evaluation maps are Y-transpose P and X-transpose Q.
Their matrix pairing is the original channel trace contraction by cyclic
trace. Sum these identities over the actual component tensors.
-/
theorem raw_contraction [Fintype Comp] (oA oB : Fin 2 → Comp → Frame B H N E)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : X) :
    fullContraction (rawForms oA oB) X i z x =
      profileContraction (oB z) (profileMap (oA i) x.val) := by
  simp only [fullContraction, profileContraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply, raw_plus, raw_minus]
  apply Finset.sum_congr rfl
  intro e _
  exact channel_contraction (oA i e) (oB z e) (x.val e)

/--
---
conclusion: Lax342547.RawContractions.raw_star_contraction
---
If the actual cross Grams extend the whole numerical table, first use
extension independence on effective profiles, then identify the full
contraction with the model's original frame tensor contraction.
-/
theorem raw_star_contraction [Fintype Comp] (oA oB : Fin 2 → Comp → Frame B H N E)
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (hT : Lax342547.TableContractions.Extends (rawForms oA oB) T)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : effective X P i) :
    starContraction T X i z x = profileContraction (oB z) (profileMap (oA i) x.val.val) := by
  rw [Lax342547.TableContractions.star_extension T _ hT, Lax342547.RawContractions.raw_contraction]

end Lax342547Proofs.RawContractions
