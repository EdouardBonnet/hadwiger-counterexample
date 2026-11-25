import Lax793645Proofs.Simplifications.QuadraticGramCodes
import Lax793645Proofs.Simplifications.QuadraticTargetSolvability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

theorem quadratic_code_transpose (M : Mat I I) : quadraticGramCode Mᵀ=quadraticGramCode M := by
  apply Subtype.ext
  funext v
  exact evmat_transpose M v v

theorem quadratic_code_cross_zero (M : Mat I I) : quadraticGramCode (M+Mᵀ)=0 := by
  rw [map_add,quadratic_code_transpose,char_two]

/-- Characters of quadratic Gram data have symmetric ordered coefficient
matrices. Arbitrary ordered Gram characters would impose extra constraints. -/
theorem quadratic_character_representation (φ : QuadraticGramCode I→ₗ[F]F) :
    ∃ M : Mat I I,Mᵀ=M ∧mpair M=φ.comp quadraticGramCode := by
  obtain ⟨M,hM⟩:=matrix_functional_representation (φ.comp quadraticGramCode)
  refine ⟨M,?_,hM⟩
  apply evmat_ext
  intro x y
  rw [evmat_transpose]
  have hz : evmat M x y+evmat M y x=0 := by
    rw [←mpair_outer,←mpair_outer,←map_add,←transpose_vecMulVec x y,hM]
    change φ (quadraticGramCode (vecMulVec x y+(vecMulVec x y)ᵀ))=0
    rw [quadratic_code_cross_zero,map_zero]
  exact add_left_cancel (hz.trans (char_two (evmat M x y)).symm)

/-- A matrix whose diagonal quadratic evaluation vanishes is symmetric
with zero diagonal, over the binary field. -/
theorem quadratic_code_zero_data (G : Mat I I) (hG : quadraticGramCode G=0) :
    Gᵀ=G ∧∀ i,G i i=0 := by
  have hz (v : Vec I) : evmat G v v=0 := congrFun (congrArg Subtype.val hG) v
  constructor
  · apply evmat_ext
    intro x y
    rw [evmat_transpose]
    have hxy:=hz (x+y)
    simp only [evmat,Matrix.mulVec_add,add_dotProduct,dotProduct_add] at hxy
    have hx:=hz x
    have hy:=hz y
    change dotProduct x (G*ᵥx)=0 at hx
    change dotProduct y (G*ᵥy)=0 at hy
    rw [hx,hy,zero_add,add_zero] at hxy
    exact add_right_cancel (hxy.trans (char_two (evmat G x y)).symm)
  · intro i
    simpa [evmat] using hz (Pi.single i 1)

/-- Symmetric coefficient matrices annihilate every redundant quadratic
Gram equation, including in characteristic two. -/
theorem symmetric_pairing_quadratic_kernel (M G : Mat I I) (hM : Mᵀ=M)
    (hG : quadraticGramCode G=0) : mpair M G=0 := by
  obtain ⟨hS,hD⟩:=quadratic_code_zero_data G hG
  change (∑ i,∑ j,M i j*G i j)=0
  have he : (∑ z : I×I,M z.1 z.2*G z.1 z.2)=∑ i,∑ j,M i j*G i j :=
    Fintype.sum_prod_type _
  rw [←he]
  apply Finset.sum_ninvolution Prod.swap
  · rintro ⟨i,j⟩
    have hm : M j i=M i j:=congrFun (congrFun hM i) j
    have hg : G j i=G i j:=congrFun (congrFun hS i) j
    change M i j*G i j+M j i*G j i=0
    rw [hm,hg,char_two]
  · rintro ⟨i,j⟩ h he
    have hij : j=i:=congrArg Prod.fst he
    subst j
    exact h (by rw [hD,mul_zero])
  · intro x
    exact mem_univ _
  · intro x
    exact Prod.swap_swap x

/-- A symmetric Gram character is constant on a prescribed quadratic
Gram fiber; no ordered Gram refinement is needed. -/
theorem symmetric_pairing_quadratic_code (M G H : Mat I I) (hM : Mᵀ=M)
    (hGH : quadraticGramCode G=quadraticGramCode H) : mpair M G=mpair M H := by
  have hz : quadraticGramCode (G+H)=0 := by rw [map_add,hGH,char_two]
  have hh:=symmetric_pairing_quadratic_kernel M (G+H) hM hz
  rw [map_add] at hh
  exact add_left_cancel (hh.trans (char_two (mpair M G)).symm) |>.symm

end
end Lax793645Proofs.Simplifications
