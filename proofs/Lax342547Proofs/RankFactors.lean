import Lax342547.RankFactors
import Lax342547Proofs.ProductImages

namespace Lax342547Proofs.RankFactors
open Lax342547.RankFactors

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.RankFactors.independent_rank_factors
---
-/
theorem independent_rank_factors {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) :
    ∃ A : Matrix I (Fin C.rank) Binary, ∃ B : Matrix J (Fin C.rank) Binary,
      A * B.transpose = C ∧ Function.Injective A.mulVec ∧ Function.Injective B.mulVec := by
  classical
  let f := C.mulVecLin
  let S := LinearMap.range f
  let e := (Module.finBasis Binary S).equivFun
  let a := S.subtype.comp e.symm.toLinearMap
  let b := e.toLinearMap.comp f.rangeRestrict
  have ha : Function.Injective a := S.injective_subtype.comp e.symm.injective
  have hb : Function.Surjective b := e.surjective.comp f.surjective_rangeRestrict
  have hab : a.comp b = f := by
    apply LinearMap.ext
    intro v
    change (e.symm (e (f.rangeRestrict v))).val = f v
    simp
  let A := a.toMatrix'
  let B := b.toMatrix'.transpose
  refine ⟨A, B, ?_, ?_, ?_⟩
  · change a.toMatrix' * b.toMatrix'.transpose.transpose = C
    rw [Matrix.transpose_transpose, ← LinearMap.toMatrix'_comp, hab]
    exact Lax342547Proofs.PairedFrames.toMatrix_mulVecLin C
  · intro x y h
    apply ha
    change a.toMatrix'.mulVec x = a.toMatrix'.mulVec y at h
    simpa only [LinearMap.toMatrix'_mulVec] using h
  · have hr : b.toMatrix'.rank = C.rank := by
      change Module.finrank Binary (LinearMap.range b.toMatrix'.mulVecLin) = _
      have heq : b.toMatrix'.mulVecLin = b := by
        apply LinearMap.ext
        intro v
        simp
      rw [heq, LinearMap.range_eq_top.mpr hb, finrank_top]
      simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rfl
    have hn := B.mulVecLin.finrank_range_add_finrank_ker
    have hbr : B.rank = C.rank := by
      dsimp [B]
      rw [Matrix.rank_transpose, hr]
    have hk : Module.finrank Binary (LinearMap.ker B.mulVecLin) = 0 := by
      change B.rank + Module.finrank Binary (LinearMap.ker B.mulVecLin) = _ at hn
      rw [hbr] at hn
      simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hn
      change C.rank + Module.finrank Binary (LinearMap.ker B.mulVecLin) = C.rank at hn
      omega
    exact LinearMap.ker_eq_bot.mp ((Submodule.finrank_eq_zero.mp hk))

end Lax342547Proofs.RankFactors
