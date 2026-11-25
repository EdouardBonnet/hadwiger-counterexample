import Lax793645Proofs.Simplifications.QuadraticGramCharacters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

theorem quadratic_code_zero_of_data (G : Mat I I) (hS : Gᵀ=G) (hD : ∀ i,G i i=0) :
    quadraticGramCode G=0 := by
  apply Subtype.ext
  funext v
  change evmat G v v=0
  simp only [evmat,dotProduct,mulVec,Finset.mul_sum]
  have he : (∑ z : I×I,v z.1*(G z.1 z.2*v z.2))=
      ∑ i,∑ j,v i*(G i j*v j):=Fintype.sum_prod_type _
  rw [←he]
  apply Finset.sum_ninvolution Prod.swap
  · rintro ⟨i,j⟩
    have hs : G j i=G i j:=congrFun (congrFun hS i) j
    change v i*(G i j*v j)+v j*(G j i*v i)=0
    rw [hs]
    have he : v j*(G i j*v i)=v i*(G i j*v j):=by ring
    rw [he,char_two]
  · rintro ⟨i,j⟩ h he
    have hij : j=i:=congrArg Prod.fst he
    subst j
    exact h (by simp only [hD,zero_mul,mul_zero])
  · intro x
    exact mem_univ _
  · intro x
    exact Prod.swap_swap x

/-- Quadratic Gram equality asks for diagonal values and polar sums,
not for both ordered off-diagonal values separately. -/
theorem quadratic_code_diagonal (G : Mat I I) (d : I→F) :
    quadraticGramCode G=quadraticGramCode (Matrix.diagonal d) ↔
      (∀ i,G i i=d i) ∧∀ i j,i≠j→G i j+G j i=0 := by
  constructor
  · intro h
    have hz : quadraticGramCode (G+Matrix.diagonal d)=0 := by rw [map_add,h,char_two]
    obtain ⟨hS,hD⟩:=quadratic_code_zero_data _ hz
    constructor
    · intro i
      have hh:=hD i
      simp only [Matrix.add_apply,Matrix.diagonal_apply_eq] at hh
      exact (add_left_cancel (hh.trans (char_two (G i i)).symm)).symm
    · intro i j hij
      have hh:=congrFun (congrFun hS i) j
      simp only [Matrix.transpose_apply,Matrix.add_apply,Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ hij.symm,add_zero] at hh
      rw [hh,char_two]
  · rintro ⟨hD,hS⟩
    have hz : quadraticGramCode (G+Matrix.diagonal d)=0 := by
      apply quadratic_code_zero_of_data
      · ext i j
        by_cases hij : i=j
        · subst j; rfl
        have hh:=hS i j hij
        have he : G j i=G i j:=add_left_cancel (hh.trans (char_two (G i j)).symm)
        simp only [Matrix.transpose_apply,Matrix.add_apply,Matrix.diagonal_apply_ne _ hij,
          Matrix.diagonal_apply_ne _ (Ne.symm hij),add_zero,he]
      · intro i
        simp only [Matrix.add_apply,Matrix.diagonal_apply_eq,hD,char_two]
    rw [map_add] at hz
    exact (add_left_cancel (hz.trans (char_two (quadraticGramCode G)).symm)).symm

end
end Lax793645Proofs.Simplifications
