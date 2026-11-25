import Lax793645Proofs.Simplifications.BlockRankCompletion

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Repair the diagonal blocks of a low-rank completion to be symmetric.
The antisymmetric part is already low rank. Masking one triangle within
each fixed-size block repairs it at a constant additional rank cost. -/
theorem symmetric_patterned_block_completion
    (P : J→J→Prop) [DecidableRel P] (hP : ∀ u v,P u v→P v u)
    (M : Avenue I J) (hM : ∀ x y,¬P x.2 y.2→M x y=0) (hs : Mᵀ=M) :
    ∃ D R : Avenue I J,M=D+R ∧Dᵀ=D ∧Rᵀ=R ∧
      (∀ x y,x.1≠y.1→D x y=0) ∧
      (∀ x y,¬P x.2 y.2→D x y=0 ∧R x y=0) ∧
      R.rank≤(1+2*Fintype.card J)*(Fintype.card J*(1+4*Fintype.card J))*peak M := by
  classical
  obtain ⟨D,R,hDR,hD,hmask,hR⟩:=patterned_block_rank_completion P M hM
  let e:=Fintype.equivFin J
  let C:=maskBlockPattern (fun u v=>e u<e v) (D+Dᵀ)
  have hC (x y : I×J) : C x y=if e x.2<e y.2 then D x y+D y x else 0:=rfl
  have hblock (x y : I×J) (hxy : x.1≠y.1) : C x y=0 := by
    rw [hC,hD x y hxy,hD y x hxy.symm]
    simp
  have hsym : (D+C)ᵀ=D+C := by
    ext x y
    change D y x+C y x=D x y+C x y
    by_cases hxy : x.1=y.1
    · rcases lt_trichotomy (e x.2) (e y.2) with h|h|h
      · rw [hC,hC,if_pos h,if_neg (not_lt_of_ge h.le)]
        simp only [add_zero,←add_assoc,char_two,zero_add]
      · have h2 : x.2=y.2:=e.injective h
        have he : x=y:=Prod.ext hxy h2
        rw [he]
      · rw [hC,hC,if_pos h,if_neg (not_lt_of_ge h.le)]
        simp only [add_zero,←add_assoc,char_two,zero_add]
    · rw [hD x y hxy,hD y x (Ne.symm hxy),hblock x y hxy,hblock y x (Ne.symm hxy)]
  have he : D=M+R := by rw [hDR,add_assoc,char_two,add_zero]
  have hanti : D+Dᵀ=R+Rᵀ := by
    rw [he,transpose_add,hs]
    calc
      M+R+(M+Rᵀ)=(M+M)+(R+Rᵀ):=by abel
      _=R+Rᵀ:=by rw [char_two,zero_add]
  have hrankC : C.rank≤2*Fintype.card J*R.rank := by
    have hc : C.rank≤Fintype.card J*(D+Dᵀ).rank:=
      mask_block_rank (fun u v=>e u<e v) (D+Dᵀ)
    have hr:=mrk_add_le R Rᵀ
    rw [rank_transpose] at hr
    calc
      C.rank≤Fintype.card J*(D+Dᵀ).rank:=hc
      _=Fintype.card J*(R+Rᵀ).rank:=by rw [hanti]
      _≤2*Fintype.card J*R.rank:=by
        nlinarith [Nat.mul_le_mul_left (Fintype.card J) hr]
  have heq : M=(D+C)+(R+C) := by
    calc
      M=D+R:=hDR
      _=(D+R)+(C+C):=by rw [char_two,add_zero]
      _=(D+C)+(R+C):=by abel
  refine ⟨D+C,R+C,heq,hsym,?_,?_,?_,?_⟩
  · have hrem : R+C=M+(D+C) := by rw [heq,add_comm (D+C),add_assoc,char_two,add_zero]
    rw [hrem,transpose_add,hs,hsym]
  · intro x y hxy
    simp only [Matrix.add_apply,hD x y hxy,hblock x y hxy,add_zero]
  · intro x y hxy
    have hyx : ¬P y.2 x.2:=fun h=>hxy (hP _ _ h)
    have hc : C x y=0 := by rw [hC,(hmask x y hxy).1,(hmask y x hyx).1]; simp
    simp only [Matrix.add_apply,(hmask x y hxy).1,(hmask x y hxy).2,hc,add_zero,and_self]
  · have hr:=mrk_add_le R C
    have hh:=Nat.mul_le_mul_left (1+2*Fintype.card J) hR
    nlinarith

end
end Lax793645Proofs.Simplifications
