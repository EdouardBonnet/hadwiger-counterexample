import Lax342547.QuotientFactors
import Lax342547.RankFactors

namespace Lax342547Proofs.QuotientFactors
open Lax342547.QuotientFactors

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.QuotientFactors.factor_range
---
-/
theorem factor_range {I J R : Type} [Fintype I] [Fintype J] [Fintype R]
    (C : Matrix I J Binary) (A : Matrix I R Binary) (B : Matrix J R Binary)
    (hC : A * B.transpose = C) (hA : Function.Injective A.mulVec)
    (hr : Fintype.card R = C.rank) : LinearMap.range A.mulVecLin = LinearMap.range C.mulVecLin := by
  have hle : LinearMap.range C.mulVecLin ≤ LinearMap.range A.mulVecLin := by
    rw [← hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hdim : Module.finrank Binary (LinearMap.range C.mulVecLin) =
      Module.finrank Binary (LinearMap.range A.mulVecLin) := by
    rw [LinearMap.finrank_range_of_inj (f := A.mulVecLin) hA]
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    exact hr.symm
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

/--
---
conclusion: Lax342547.QuotientFactors.projection_range_quotient_injective
---
-/
theorem projection_range_quotient_injective {V U : Type}
    [AddCommGroup V] [Module Binary V] [AddCommGroup U] [Module Binary U]
    (D : Submodule Binary V) (p : V →ₗ[Binary] V)
    (hp : LinearMap.ker p = D) (hpid : p.comp p = p)
    (A : U →ₗ[Binary] V) (hA : Function.Injective A)
    (hrange : LinearMap.range A ≤ LinearMap.range p) : Function.Injective (D.mkQ.comp A) := by
  have hfix : p.comp A = A := by
    apply LinearMap.ext
    intro u
    obtain ⟨v, hv⟩ := hrange (LinearMap.mem_range_self A u)
    change p (A u) = A u
    rw [← hv]
    exact LinearMap.congr_fun hpid v
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro u hu
    have hd : A u ∈ D := (Submodule.Quotient.mk_eq_zero _).mp hu
    rw [← hp] at hd
    have hz : A u = 0 := by
      rw [← LinearMap.congr_fun hfix u]
      exact hd
    have hu0 : u = 0 := hA (by simpa using hz)
    simpa only [Submodule.mem_bot] using hu0
  · exact bot_le

/--
---
conclusion: Lax342547.QuotientFactors.quotient_independent_factors
---
-/
theorem quotient_independent_factors {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : LinearMap.ker p = D) (hq : LinearMap.ker q = E)
    (hpid : p.comp p = p) (hqid : q.comp q = q) : by
      classical
      let Z := p.toMatrix' * C * q.toMatrix'.transpose
      exact ∃ A : Matrix I (Fin Z.rank) Binary, ∃ B : Matrix I (Fin Z.rank) Binary,
        A * B.transpose = Z ∧ Function.Injective (D.mkQ.comp A.mulVecLin) ∧
          Function.Injective (E.mkQ.comp B.mulVecLin) := by
  classical
  let Z := p.toMatrix' * C * q.toMatrix'.transpose
  obtain ⟨A, B, hAB, hA, hB⟩ := Lax342547.RankFactors.independent_rank_factors Z
  have hArange := Lax342547.QuotientFactors.factor_range Z A B hAB hA (Fintype.card_fin _)
  have hBprod : B * A.transpose = Z.transpose := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hAB
  have hBrange := Lax342547.QuotientFactors.factor_range Z.transpose B A hBprod hB
    (by rw [Matrix.rank_transpose, Fintype.card_fin])
  have hprange : LinearMap.range Z.mulVecLin ≤ LinearMap.range p := by
    have he : Z.mulVecLin = p.comp (C * q.toMatrix'.transpose).mulVecLin := by
      dsimp only [Z]
      rw [Matrix.mul_assoc, Matrix.mulVecLin_mul]
      congr 1
      apply LinearMap.ext
      intro v
      simp
    rw [he]
    exact LinearMap.range_comp_le_range _ _
  have hqrange : LinearMap.range Z.transpose.mulVecLin ≤ LinearMap.range q := by
    have he : Z.transpose.mulVecLin = q.comp (C.transpose * p.toMatrix'.transpose).mulVecLin := by
      dsimp only [Z]
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.mulVecLin_mul]
      congr 1
      apply LinearMap.ext
      intro v
      simp
    rw [he]
    exact LinearMap.range_comp_le_range _ _
  refine ⟨A, B, hAB, ?_, ?_⟩
  · exact Lax342547.QuotientFactors.projection_range_quotient_injective D p hp hpid A.mulVecLin hA
      (hArange.le.trans hprange)
  · exact Lax342547.QuotientFactors.projection_range_quotient_injective E q hq hqid B.mulVecLin hB
      (hBrange.le.trans hqrange)

end Lax342547Proofs.QuotientFactors
