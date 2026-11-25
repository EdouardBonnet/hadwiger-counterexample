import Lax793645Proofs.Simplifications.QuadraticTargetSolvability
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PrimalSpaceCompression

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem quadratic_pull_apply {I : Type} [Fintype I] [DecidableEq I]
    (A M : Mat I I) (v : Vec I) :
    (pullM A A M).toQuadraticForm' v=M.toQuadraticForm' (A*ᵥv) := by
  change Matrix.toBilin' (pullM A A M) v v=Matrix.toBilin' M (A*ᵥv) (A*ᵥv)
  simp only [Matrix.toBilin'_apply']
  exact evmat_pull A A M v v

theorem quadratic_pull_polar {I : Type} [Fintype I] [DecidableEq I]
    (A M : Mat I I) (v w : Vec I) :
    (pullM A A M).toQuadraticForm'.polarBilin v w=
      M.toQuadraticForm'.polarBilin (A*ᵥv) (A*ᵥw) := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    quadratic_pull_apply,Matrix.mulVec_add]

variable {p : Shape} {n : ℕ}

def cutMatrixFunctional (M : Profile p n) : Profile p n→ₗ[F]F :=
  ∑ e,(mpair (M e)).comp (LinearMap.proj e)

theorem cut_matrix_functional_apply (M x : Profile p n) :
    cutMatrixFunctional M x=∑ e,mpair (M e) (x e) := by
  simp only [cutMatrixFunctional,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

/-- Compress the residual quadratic target in the actual cut-profile space.
The compression fixes the frozen primal vectors, and hence preserves both
the frozen quadratic values and the kernel polar rows. -/
theorem quadratic_cut_compression
    (P K : Comp p.g→Space (Ray p n)) (M Q : Profile p n)
    (f r : ℕ) (hP : ∀ e,dim (P e)≤f) (hK : ∀ e,K e≤P e)
    (hM : ∀ e,(M e).rank≤r)
    (hval : ∀ e,∀ v∈P e,(Q e).toQuadraticForm' v=0)
    (hrow : ∀ e,∀ k∈K e,∀ v,(Q e).toQuadraticForm'.polarBilin k v=0)
    (hobs : ∀ x∈Xspace p n,cutMatrixFunctional Q x=cutMatrixFunctional M x) :
    ∃ Q' : Profile p n,
      (∀ e,∀ v∈P e,(Q' e).toQuadraticForm' v=0) ∧
      (∀ e,∀ k∈K e,∀ v,(Q' e).toQuadraticForm'.polarBilin k v=0) ∧
      (∀ x∈Xspace p n,cutMatrixFunctional Q' x=cutMatrixFunctional Q x) ∧
      ∀ e,(Q' e).rank≤drow p f r := by
  classical
  let duals (z : Place p):=colSp (if z.2 then M z.1 else (M z.1)ᵀ)
  have hd (z : Place p) : dim (duals z)≤r := by
    cases z with
    | mk e b => cases b <;> simp only [duals,Bool.false_eq_true,if_false,if_true,colSp_dim,
        Matrix.rank_transpose] <;> exact hM e
  obtain ⟨A,hfix,hdual,hrank⟩:=shrink_both (fun z : Place p=>P z.1) duals f r
    (fun z=>hP z.1) hd
  let D:=rowShrink p A
  have hm (e : Comp p.g) : pullM D D (M e)=M e := by
    have hl : Dᵀ*M e=M e:=mat_mul_fix (hdual (e,true))
    have hh := congrArg Matrix.transpose (mat_mul_fix (hdual (e,false)))
    rw [pullM_def,hl]
    simpa only [Bool.false_eq_true,if_false,Matrix.transpose_mul,Matrix.transpose_transpose] using hh
  let Q' (e : Comp p.g):=pullM D D (Q e)
  refine ⟨Q',?_,?_,?_,?_⟩
  · intro e v hv
    change (pullM D D (Q e)).toQuadraticForm' v=0
    rw [quadratic_pull_apply,hfix (e,true) v hv]
    exact hval e v hv
  · intro e k hk v
    change (pullM D D (Q e)).toQuadraticForm'.polarBilin k v=0
    rw [quadratic_pull_polar,hfix (e,true) k (hK e hk)]
    exact hrow e k hk _
  · intro x hx
    let y : Profile p n:=fun e=>liftM D D (x e)
    have hy : y∈Xspace p n:=shrink_X A x hx
    have he:=hobs y hy
    have pull (B : Profile p n) :
        cutMatrixFunctional B y=∑ e,mpair (pullM D D (B e)) (x e) := by
      rw [cut_matrix_functional_apply]
      exact Finset.sum_congr rfl (fun e _=>mpair_liftM D D (B e) (x e))
    rw [pull,pull] at he
    simp_rw [hm] at he
    calc
      cutMatrixFunctional Q' x=cutMatrixFunctional M x:=by
        simpa only [cut_matrix_functional_apply] using he
      _ = cutMatrixFunctional Q x:=(hobs x hx).symm
  · intro e
    change (pullM D D (Q e)).rank≤_
    rw [pullM_def]
    exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans
      (by rw [Matrix.rank_transpose]; exact hrank)

end
end Lax793645Proofs.Simplifications
