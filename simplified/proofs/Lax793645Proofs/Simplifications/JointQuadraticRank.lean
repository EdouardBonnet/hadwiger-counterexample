import Lax793645Proofs.Simplifications.JointQuadraticCompression

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

/-- The bounded-rank target assembly for the joint primal cut space. A small
baseline carries the frozen data; the large explicit part is projected
away first. Only the remaining small target is compressed. -/
theorem joint_quadratic_bounded_target
    (P K : Comp p.g→Space (JointRay p n)) (M B Q : JointProfile p n)
    (f b r : ℕ) (hP : ∀ e,dim (P e)≤f) (hK : ∀ e,K e≤P e)
    (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v∈P e,(Q e).toQuadraticForm' v=(B e).toQuadraticForm' v)
    (hrow : ∀ e,∀ k∈K e,∀ v,(Q e).toQuadraticForm'.polarBilin k v=
      (B e).toQuadraticForm'.polarBilin k v)
    (hobs : ∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) :
    ∃ Q' : JointProfile p n,
      (∀ e,∀ v∈P e,(Q' e).toQuadraticForm' v=(B e).toQuadraticForm' v) ∧
      (∀ e,∀ k∈K e,∀ v,(Q' e).toQuadraticForm'.polarBilin k v=
        (B e).toQuadraticForm'.polarBilin k v) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q' x=jointMatrixFunctional M x) ∧
      ∀ e,(Q' e).rank≤r+b+jointCompressionRank p f (2*f+b) := by
  classical
  choose V hvRank hvResidual hvVal hvRow using fun e=>quadratic_project_away (P e) (M e)
  let M₀:=M+V+B
  let Q₀:=Q+V+B
  have hM₀ (e : Comp p.g) : (M₀ e).rank≤2*f+b :=
    (mrk_add_le ..).trans (Nat.add_le_add ((hvResidual e).trans (Nat.mul_le_mul_left 2 (hP e))) (hB e))
  have hQ₀ (e : Comp p.g) (v : JointRay p n) (hv : v∈P e) : (Q₀ e).toQuadraticForm' v=0 := by
    simp only [Q₀,Pi.add_apply,matrix_quadratic_add,hval e v hv,hvVal e v hv,
      add_zero,char_two]
  have hK₀ (e : Comp p.g) (k : JointRay p n) (hk : k∈K e) (v : JointRay p n) :
      (Q₀ e).toQuadraticForm'.polarBilin k v=0 := by
    simp only [Q₀,Pi.add_apply,matrix_polar_add,hrow e k hk v,hvRow e k (hK e hk) v,
      add_zero,char_two]
  have ho₀ (x : JointProfile p n) (hx : x∈jointXspace) :
      jointMatrixFunctional Q₀ x=jointMatrixFunctional M₀ x := by
    simp only [Q₀,M₀,joint_matrix_functional_add,hobs x hx]
  obtain ⟨Z,hZval,hZrow,hZobs,hZrank⟩:=joint_quadratic_compression P K M₀ Q₀
    f (2*f+b) hP hK hM₀ hQ₀ hK₀ ho₀
  refine ⟨V+B+Z,?_,?_,?_,?_⟩
  · intro e v hv
    simp only [Pi.add_apply,matrix_quadratic_add,hvVal e v hv,hZval e v hv,zero_add,add_zero]
  · intro e k hk v
    simp only [Pi.add_apply,matrix_polar_add,hvRow e k (hK e hk) v,hZrow e k hk v,
      zero_add,add_zero]
  · intro x hx
    rw [joint_matrix_functional_add,joint_matrix_functional_add,hZobs x hx]
    simp only [Q₀,joint_matrix_functional_add,hobs x hx]
    calc
      _ = jointMatrixFunctional M x+(jointMatrixFunctional V x+jointMatrixFunctional V x)+
        (jointMatrixFunctional B x+jointMatrixFunctional B x) := by abel
      _ = _ := by rw [char_two,char_two,add_zero,add_zero]
  · intro e
    exact (mrk_add_le ..).trans (Nat.add_le_add
      ((mrk_add_le ..).trans (Nat.add_le_add ((hvRank e).trans (hM e)) (hB e))) (hZrank e))


end
end Lax793645Proofs.Simplifications
