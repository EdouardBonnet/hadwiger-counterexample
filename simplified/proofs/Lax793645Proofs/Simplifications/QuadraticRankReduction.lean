import Lax793645Proofs.Simplifications.QuadraticCutCompression

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem matrix_quadratic_add (A B : Mat I I) (v : Vec I) :
    (A+B).toQuadraticForm' v=A.toQuadraticForm' v+B.toQuadraticForm' v := by
  simp only [←matrix_quadratic_outer,mpair_add]

theorem matrix_polar_add (A B : Mat I I) (v w : Vec I) :
    (A+B).toQuadraticForm'.polarBilin v w=
      A.toQuadraticForm'.polarBilin v w+B.toQuadraticForm'.polarBilin v w := by
  simp only [matrix_quadratic_polar,mpair_add]

/-- Remove the explicit gradient away from the frozen space before applying
base-coordinate compression. Only twice the frozen dimension enters the
residual, irrespective of the rank of the explicit gradient. -/
theorem quadratic_project_away (P : Space (Vec I)) (M : Mat I I) :
    ∃ V : Mat I I,V.rank≤M.rank ∧ (M+V).rank≤2*dim P ∧
      (∀ v∈P,V.toQuadraticForm' v=0) ∧
      ∀ v∈P,∀ w,V.toQuadraticForm'.polarBilin v w=0 := by
  let A:=prj P
  let B:=1-A
  let V:=pullM B B M
  have hz (v : Vec I) (hv : v∈P) : B*ᵥv=0 := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,(prj_data P).fixes v hv,sub_self]
  have hr : A.rank≤dim P:=rank_maps P (prj_data P).onto
  refine ⟨V,rank_lift_le _ _ _,?_,?_,?_⟩
  · have he : M-V=Aᵀ*M+Bᵀ*M*A := by
      dsimp only [V,B]
      rw [pullM_def]
      simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.mul_sub,Matrix.sub_mul,
        Matrix.mul_one,Matrix.one_mul]
      abel
    have hh : (M-V).rank≤2*dim P := by
      rw [he,two_mul]
      exact (mrk_add_le ..).trans (Nat.add_le_add
        ((Matrix.rank_mul_le_left ..).trans (by rw [Matrix.rank_transpose]; exact hr))
        ((Matrix.rank_mul_le_right ..).trans hr))
    simpa only [ZModModule.sub_eq_add] using hh
  · intro v hv
    rw [quadratic_pull_apply,hz v hv,map_zero]
  · intro v hv w
    rw [quadratic_pull_polar,hz v hv,map_zero,LinearMap.zero_apply]

variable {p : Shape} {n : ℕ}

theorem cut_matrix_functional_add (A B x : Profile p n) :
    cutMatrixFunctional (A+B) x=cutMatrixFunctional A x+cutMatrixFunctional B x := by
  simp only [cut_matrix_functional_apply,Pi.add_apply,mpair_add,Finset.sum_add_distrib]

/-- The bounded-rank target assembly for one primal cut space. A small
baseline carries the frozen data; the large explicit part is projected
away first. Only the remaining small target is compressed. -/
theorem quadratic_bounded_cut_target
    (P K : Comp p.g→Space (Ray p n)) (M B Q : Profile p n)
    (f b r : ℕ) (hP : ∀ e,dim (P e)≤f) (hK : ∀ e,K e≤P e)
    (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v∈P e,(Q e).toQuadraticForm' v=(B e).toQuadraticForm' v)
    (hrow : ∀ e,∀ k∈K e,∀ v,(Q e).toQuadraticForm'.polarBilin k v=
      (B e).toQuadraticForm'.polarBilin k v)
    (hobs : ∀ x∈Xspace p n,cutMatrixFunctional Q x=cutMatrixFunctional M x) :
    ∃ Q' : Profile p n,
      (∀ e,∀ v∈P e,(Q' e).toQuadraticForm' v=(B e).toQuadraticForm' v) ∧
      (∀ e,∀ k∈K e,∀ v,(Q' e).toQuadraticForm'.polarBilin k v=
        (B e).toQuadraticForm'.polarBilin k v) ∧
      (∀ x∈Xspace p n,cutMatrixFunctional Q' x=cutMatrixFunctional M x) ∧
      ∀ e,(Q' e).rank≤r+b+drow p f (2*f+b) := by
  classical
  choose V hvRank hvResidual hvVal hvRow using fun e=>quadratic_project_away (P e) (M e)
  let M₀:=M+V+B
  let Q₀:=Q+V+B
  have hM₀ (e : Comp p.g) : (M₀ e).rank≤2*f+b :=
    (mrk_add_le ..).trans (Nat.add_le_add ((hvResidual e).trans (Nat.mul_le_mul_left 2 (hP e))) (hB e))
  have hQ₀ (e : Comp p.g) (v : Ray p n) (hv : v∈P e) : (Q₀ e).toQuadraticForm' v=0 := by
    simp only [Q₀,Pi.add_apply,matrix_quadratic_add,hval e v hv,hvVal e v hv,
      add_zero,char_two]
  have hK₀ (e : Comp p.g) (k : Ray p n) (hk : k∈K e) (v : Ray p n) :
      (Q₀ e).toQuadraticForm'.polarBilin k v=0 := by
    simp only [Q₀,Pi.add_apply,matrix_polar_add,hrow e k hk v,hvRow e k (hK e hk) v,
      add_zero,char_two]
  have ho₀ (x : Profile p n) (hx : x∈Xspace p n) :
      cutMatrixFunctional Q₀ x=cutMatrixFunctional M₀ x := by
    simp only [Q₀,M₀,cut_matrix_functional_add,hobs x hx]
  obtain ⟨Z,hZval,hZrow,hZobs,hZrank⟩:=quadratic_cut_compression P K M₀ Q₀
    f (2*f+b) hP hK hM₀ hQ₀ hK₀ ho₀
  refine ⟨V+B+Z,?_,?_,?_,?_⟩
  · intro e v hv
    simp only [Pi.add_apply,matrix_quadratic_add,hvVal e v hv,hZval e v hv,zero_add,add_zero]
  · intro e k hk v
    simp only [Pi.add_apply,matrix_polar_add,hvRow e k (hK e hk) v,hZrow e k hk v,
      zero_add,add_zero]
  · intro x hx
    rw [cut_matrix_functional_add,cut_matrix_functional_add,hZobs x hx]
    simp only [Q₀,cut_matrix_functional_add,hobs x hx]
    calc
      _ = cutMatrixFunctional M x+(cutMatrixFunctional V x+cutMatrixFunctional V x)+
        (cutMatrixFunctional B x+cutMatrixFunctional B x) := by abel
      _ = _ := by rw [char_two,char_two,add_zero,add_zero]
  · intro e
    exact (mrk_add_le ..).trans (Nat.add_le_add
      ((mrk_add_le ..).trans (Nat.add_le_add ((hvRank e).trans (hM e)) (hB e))) (hZrank e))

end
end Lax793645Proofs.Simplifications
