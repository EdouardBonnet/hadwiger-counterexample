import Lax793645Proofs.Simplifications.JointQuadraticSpace

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

def jointCompressionRank (p : Shape) (f r : ℕ) : ℕ:=2*drow p (2*f) (2*r)

theorem joint_shrink_xspace (A : Nendo p n) (x : JointProfile p n)
    (hx : x∈jointXspace) :
    (fun e=>liftM (blockDiagonal (fun _ : Bool=>rowShrink p A))
      (blockDiagonal (fun _ : Bool=>rowShrink p A)) (x e))∈jointXspace := by
  obtain ⟨y,hy,rfl⟩:=(joint_xspace_mem x).mp hx
  have he : (fun e=>liftM (blockDiagonal (fun _ : Bool=>rowShrink p A))
      (blockDiagonal (fun _ : Bool=>rowShrink p A)) (jointCutEmbed y e))=
      jointCutEmbed (fun i e=>liftM (rowShrink p A) (rowShrink p A) (y i e)) := by
    funext e
    exact joint_diagonal_lift _ _
  rw [he]
  exact joint_cut_in_space _ (fun i=>shrink_X A (y i) (hy i))

/-- Compression on both endpoint blocks fixes the entire frozen space,
including vectors and kernel relations mixing the endpoints. -/
theorem joint_quadratic_compression
    (P K : Comp p.g→Space (JointRay p n)) (M Q : JointProfile p n)
    (f r : ℕ) (hP : ∀ e,dim (P e)≤f) (hK : ∀ e,K e≤P e)
    (hM : ∀ e,(M e).rank≤r)
    (hval : ∀ e,∀ v∈P e,(Q e).toQuadraticForm' v=0)
    (hrow : ∀ e,∀ k∈K e,∀ v,(Q e).toQuadraticForm'.polarBilin k v=0)
    (hobs : ∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) :
    ∃ Q' : JointProfile p n,
      (∀ e,∀ v∈P e,(Q' e).toQuadraticForm' v=0) ∧
      (∀ e,∀ k∈K e,∀ v,(Q' e).toQuadraticForm'.polarBilin k v=0) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q' x=jointMatrixFunctional Q x) ∧
      ∀ e,(Q' e).rank≤jointCompressionRank p f r := by
  classical
  let duals (z : Place p):=colSp (if z.2 then M z.1 else (M z.1)ᵀ)
  have hd (z : Place p) : dim (duals z)≤r := by
    cases z with
    | mk e b => cases b <;> simp only [duals,Bool.false_eq_true,if_false,if_true,colSp_dim,
        Matrix.rank_transpose] <;> exact hM e
  obtain ⟨A,hfix,hdual,hrank⟩:=shrink_both
    (fun z : Place p=>jointProjectionCover (P z.1))
    (fun z=>jointProjectionCover (duals z)) (2*f) (2*r)
    (fun z=>(joint_projection_cover_dimension _).trans (Nat.mul_le_mul_left 2 (hP z.1)))
    (fun z=>(joint_projection_cover_dimension _).trans (Nat.mul_le_mul_left 2 (hd z)))
  let D:=blockDiagonal (fun _ : Bool=>rowShrink p A)
  have hfix' (e : Comp p.g) : ∀ v∈P e,D*ᵥv=v :=
    joint_diagonal_fixes _ _ (fun i v hv=>hfix (e,true) v (joint_projection_le_cover _ i hv))
  have hdual' (z : Place p) : ∀ v∈duals z,Dᵀ*ᵥv=v := by
    change ∀ v∈duals z,(blockDiagonal (fun _ : Bool=>rowShrink p A))ᵀ*ᵥv=v
    rw [Matrix.blockDiagonal_transpose]
    exact joint_diagonal_fixes _ _ (fun i v hv=>hdual z v (joint_projection_le_cover _ i hv))
  have hrank' : D.rank≤jointCompressionRank p f r := by
    have hh:=(joint_diagonal_rank_le (fun _ : Bool=>rowShrink p A)).trans
      (Finset.sum_le_sum (fun _ _=>hrank))
    simpa [D,jointCompressionRank] using hh
  have hm (e : Comp p.g) : pullM D D (M e)=M e := by
    have hl : Dᵀ*M e=M e:=mat_mul_fix (hdual' (e,true))
    have hh:=congrArg Matrix.transpose (mat_mul_fix (hdual' (e,false)))
    rw [pullM_def,hl]
    simpa only [Bool.false_eq_true,if_false,Matrix.transpose_mul,Matrix.transpose_transpose] using hh
  let Q' (e : Comp p.g):=pullM D D (Q e)
  refine ⟨Q',?_,?_,?_,?_⟩
  · intro e v hv
    change (pullM D D (Q e)).toQuadraticForm' v=0
    rw [quadratic_pull_apply,hfix' e v hv]
    exact hval e v hv
  · intro e k hk v
    change (pullM D D (Q e)).toQuadraticForm'.polarBilin k v=0
    rw [quadratic_pull_polar,hfix' e k (hK e hk)]
    exact hrow e k hk _
  · intro x hx
    let y : JointProfile p n:=fun e=>liftM D D (x e)
    have hy : y∈jointXspace:=joint_shrink_xspace A x hx
    have he:=hobs y hy
    have pull (B : JointProfile p n) :
        jointMatrixFunctional B y=∑ e,mpair (pullM D D (B e)) (x e) := by
      rw [joint_matrix_functional_apply]
      exact Finset.sum_congr rfl (fun e _=>mpair_liftM D D (B e) (x e))
    rw [pull,pull] at he
    simp_rw [hm] at he
    calc
      jointMatrixFunctional Q' x=jointMatrixFunctional M x:=by
        simpa only [joint_matrix_functional_apply] using he
      _ = jointMatrixFunctional Q x:=(hobs x hx).symm
  · intro e
    change (pullM D D (Q e)).rank≤_
    rw [pullM_def]
    exact ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_left ..)).trans
      (by rw [Matrix.rank_transpose]; exact hrank')

end
end Lax793645Proofs.Simplifications
