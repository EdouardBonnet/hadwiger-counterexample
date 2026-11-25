import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Lax793645Proofs.Simplifications
noncomputable section
variable {B : Type} [AddCommGroup B] [Module (ZMod 2) B]

/-- On the polar radical a binary quadratic form is linear. -/
def radicalLinear (Q : QuadraticForm (ZMod 2) B) :
    Q.polarBilin.ker →ₗ[ZMod 2] ZMod 2 where
  toFun x := Q x
  map_add' x y := by
    change Q ((x:B)+(y:B))=_
    rw [QuadraticMap.map_add Q]
    have h : Q.polarBilin x y=0 := by
      have hx : Q.polarBilin (x:B)=0 := x.property
      rw [hx,LinearMap.zero_apply]
    rw [←QuadraticMap.polarBilin_apply_apply,h,add_zero]
  map_smul' a x := by
    change Q (a•(x:B))=a*Q x
    rw [QuadraticMap.map_smul,smul_eq_mul]
    have ha : a*a=a := by
      rcases ((by decide : ∀ x : ZMod 2,x=0 ∨ x=1) a) with h|h <;> rw [h] <;> simp
    rw [ha]

theorem radical_codimension [FiniteDimensional (ZMod 2) B]
    (Q : QuadraticForm (ZMod 2) B) :
    Module.finrank (ZMod 2) B ≤ Module.finrank (ZMod 2) Q.polarBilin.range+
      Module.finrank (ZMod 2) Q.radical+1 := by
  let R := Q.polarBilin.ker
  let f := radicalLinear Q
  have hk : (LinearMap.ker f).map R.subtype=Q.radical := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨hy,y.property⟩
    · rintro ⟨hq,hp⟩
      exact ⟨⟨x,hp⟩,hq,rfl⟩
  have hd : Module.finrank (ZMod 2) f.ker=Module.finrank (ZMod 2) Q.radical := by
    rw [←hk]
    exact (Submodule.finrank_map_subtype_eq R f.ker).symm
  have hr : Module.finrank (ZMod 2) f.range≤1 := by
    simpa using (Submodule.finrank_le f.range)
  have h1 := f.finrank_range_add_finrank_ker
  have h2 := Q.polarBilin.finrank_range_add_finrank_ker
  rw [hd] at h1
  change Module.finrank (ZMod 2) f.range+Module.finrank (ZMod 2) Q.radical=
    Module.finrank (ZMod 2) Q.polarBilin.ker at h1
  omega

/-- Remove a zero quadratic radical while preserving every frozen vector.
The retained dimension is at most polar rank plus frozen dimension plus one. -/
theorem quadratic_radical_compression [FiniteDimensional (ZMod 2) B]
    (Q : QuadraticForm (ZMod 2) B) (S : Submodule (ZMod 2) B) :
    ∃ K : Submodule (ZMod 2) B, K≤Q.radical ∧ Disjoint K S ∧
      Module.finrank (ZMod 2) (B⧸K) ≤ Module.finrank (ZMod 2) Q.polarBilin.range+
        Module.finrank (ZMod 2) S+1 := by
  obtain ⟨C,hC⟩ := S.exists_isCompl
  let K := Q.radical⊓C
  refine ⟨K,inf_le_left,?_,?_⟩
  · exact hC.disjoint.symm.mono_left inf_le_right
  · have hR := radical_codimension Q
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq Q.radical C
    have hdim := (S.prodEquivOfIsCompl C hC).finrank_eq
    rw [Module.finrank_prod] at hdim
    have hle := Submodule.finrank_le (Q.radical⊔C)
    have hquot := Submodule.finrank_quotient_add_finrank K
    change Module.finrank (ZMod 2) (Q.radical⊔C : Submodule (ZMod 2) B)+Module.finrank (ZMod 2) K=_ at hsup
    omega
/-- Prescribe exactly the kernel lost on the frozen space while compressing
the rest of the zero quadratic radical. -/
theorem quadratic_compression_preserving_kernel [FiniteDimensional (ZMod 2) B]
    (Q : QuadraticForm (ZMod 2) B) (S K : Submodule (ZMod 2) B)
    (hKS : K≤S) (hKQ : K≤Q.radical) :
    ∃ N : Submodule (ZMod 2) B, N≤Q.radical ∧ N⊓S=K ∧
      Module.finrank (ZMod 2) (B⧸N) ≤ Module.finrank (ZMod 2) Q.polarBilin.range+
        Module.finrank (ZMod 2) S+1 := by
  obtain ⟨R,hRQ,hRS,hR⟩ := quadratic_radical_compression Q S
  refine ⟨K⊔R,sup_le hKQ hRQ,?_,?_⟩
  · rw [sup_inf_assoc_of_le R hKS,hRS.eq_bot,sup_bot_eq]
  · have hle : Module.finrank (ZMod 2) R≤Module.finrank (ZMod 2)
        (K⊔R : Submodule (ZMod 2) B) := Submodule.finrank_mono le_sup_right
    have h1 := Submodule.finrank_quotient_add_finrank R
    have h2 := Submodule.finrank_quotient_add_finrank (K⊔R)
    omega

end
end Lax793645Proofs.Simplifications
