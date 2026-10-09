import Lax342547.PairedFrames
import Lax342547Proofs.LinearExtension

namespace Lax342547Proofs.PairedFrames

universe u v w z

variable {K : Type u} {U : Type v} {V : Type w} {W : Type z} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/--
---
conclusion: Lax342547.PairedFrames.paired_frame_orbit
---
Split the two evaluation surjections into their kernels and a common
quotient. Extend the induced injection on the Gram kernel, then correct
the remaining discrepancy by a shear over the quotient. This gives the
primal automorphism and its contragredient action on every dual vector.
-/
theorem paired_frame_orbit (A A' : U →ₗ[K] V) (B B' : W →ₗ[K] Module.Dual K V)
    (hA : Function.Injective A) (hA' : Function.Injective A')
    (hB : Function.Injective B) (hB' : Function.Injective B')
    (hgram : ∀ u w, B w (A u) = B' w (A' u)) :
    ∃ L : V ≃ₗ[K] V, (∀ u, L (A u) = A' u) ∧
      ∀ w v, B w (L.symm v) = B' w v := by
  have hp : Function.Surjective B.flip := (LinearMap.flip_surjective_iff₂).mpr hB
  have hp' : Function.Surjective B'.flip := (LinearMap.flip_surjective_iff₂).mpr hB'
  have hcomm : B.flip.comp A = B'.flip.comp A' := by
    ext u w
    exact hgram u w
  obtain ⟨L, hL, hpL⟩ := LinearExtension.commuting_extension rfl A A'
    B.flip B'.flip hA hA' hp hp' hcomm
  refine ⟨L, hL, fun w v => ?_⟩
  have h := DFunLike.congr_fun (hpL (L.symm v)) w
  simpa using h.symm

@[simp] theorem toMatrix_mulVecLin {I N : Type} [Fintype I] [DecidableEq I]
    (A : Matrix N I K) : A.mulVecLin.toMatrix' = A := by
  ext i j
  simp [LinearMap.toMatrix'_apply]

theorem transpose_surjective {I N : Type} [Fintype I] [Fintype N]
    (A : Matrix N I K) (hA : Function.Injective A.mulVec) :
    Function.Surjective A.transpose.mulVec := by
  classical
  obtain ⟨f, hf⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hA)
  let U := f.toMatrix'
  have hU : U * A = 1 := by
    simpa [U, LinearMap.toMatrix'_comp] using congrArg LinearMap.toMatrix' hf
  have hAU : A.transpose * U.transpose = 1 := by simpa using congrArg Matrix.transpose hU
  intro x
  refine ⟨U.transpose.mulVec x, ?_⟩
  rw [Matrix.mulVec_mulVec, hAU, Matrix.one_mulVec]

/--
---
conclusion: Lax342547.PairedFrames.paired_matrix_orbit
---
The paired orbit in the concrete column-matrix representation. The two
ambient matrices are mutual inverses; the minus action is the transpose
of the inverse. These identities can be applied directly to raw frames.
-/
theorem paired_matrix_orbit {I J N : Type} [Fintype I] [Fintype J] [Fintype N]
    [DecidableEq N] (A A' : Matrix N I K) (B B' : Matrix N J K)
    (hA : Function.Injective A.mulVec) (hA' : Function.Injective A'.mulVec)
    (hB : Function.Injective B.mulVec) (hB' : Function.Injective B'.mulVec)
    (hgram : A.transpose * B = A'.transpose * B') :
    ∃ C D : Matrix N N K, C * D = 1 ∧ D * C = 1 ∧
      C * A = A' ∧ D.transpose * B = B' := by
  classical
  have hgram' : B.transpose * A = B'.transpose * A' := by
    simpa using congrArg Matrix.transpose hgram
  have hcomm : B.transpose.mulVecLin.comp A.mulVecLin =
      B'.transpose.mulVecLin.comp A'.mulVecLin := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hgram']
  obtain ⟨L, hL, hpL⟩ := LinearExtension.commuting_extension rfl A.mulVecLin A'.mulVecLin
    B.transpose.mulVecLin B'.transpose.mulVecLin hA hA'
    (transpose_surjective B hB) (transpose_surjective B' hB') hcomm
  let C := L.toLinearMap.toMatrix'
  let D := L.symm.toLinearMap.toMatrix'
  have hCD : C * D = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hDC : D * C = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨C, D, hCD, hDC, ?_, ?_⟩
  · have he : L.toLinearMap.comp A.mulVecLin = A'.mulVecLin := LinearMap.ext hL
    simpa [C, LinearMap.toMatrix'_comp] using congrArg LinearMap.toMatrix' he
  · have he : B'.transpose.mulVecLin.comp L.toLinearMap = B.transpose.mulVecLin :=
      LinearMap.ext hpL
    have hm : B'.transpose * C = B.transpose := by
      simpa only [LinearMap.toMatrix'_comp, toMatrix_mulVecLin] using
        congrArg LinearMap.toMatrix' he
    have hm' : B'.transpose = B.transpose * D := by
      rw [← hm, Matrix.mul_assoc, hCD, Matrix.mul_one]
    simpa using (congrArg Matrix.transpose hm').symm

end Lax342547Proofs.PairedFrames
