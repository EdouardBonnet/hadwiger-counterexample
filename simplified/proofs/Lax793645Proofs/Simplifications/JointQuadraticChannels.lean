import Lax793645Proofs.Simplifications.JointQuadraticRank
import Lax793645Proofs.Simplifications.QuadraticCutChannels
import Lax793645Proofs.Simplifications.CoordinateQuadraticExtension

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

/-- Complete the bounded-rank quadratic target and realize it by genuine
hyperbolic channel maps. This realizes the joint cut-profile space and does not
assume independence or nonvanishing of the frozen channel images. -/
theorem joint_quadratic_channels
    (h : ℕ) (P : Comp p.g→Space (JointRay p n)) (C : Comp p.g→Space (Hyperbolic h))
    (g₀ : ∀ e,P e→ₗ[F]Hyperbolic h) (ell : ∀ e,JointRay p n→ₗ[F]C e→ₗ[F]F)
    (M B : JointProfile p n) (f c b r : ℕ)
    (hP : ∀ e,dim (P e)≤f) (hC : ∀ e,dim (C e)≤c)
    (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v : P e,(B e).toQuadraticForm' v=hyperbolicQuadratic h (g₀ e v))
    (hcompat : ∀ e,∀ (v : P e) (a : C e),
      ell e v a=(hyperbolicQuadratic h).polarBilin (g₀ e v) a)
    (hrow : ∀ e,∀ (v : P e) (hv : g₀ e v∈C e) (w : JointRay p n),
      (B e).toQuadraticForm'.polarBilin v w=ell e w ⟨g₀ e v,hv⟩)
    (hobs : ∀ x∈jointXspace,
      x∈jointQuadraticConstraints P (fun e=>frozenChannelKernel h (P e) (C e) (g₀ e))→
        jointMatrixFunctional M x=jointMatrixFunctional B x)
    (hroom : r+b+jointCompressionRank p f (2*f+b)+5*c+6*f+2≤h) :
    ∃ (Q : JointProfile p n) (g : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h),
      (∀ e,∀ v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v : P e,g e v=g₀ e v) ∧
      (∀ e,∀ (v : JointRay p n) (a : C e),(hyperbolicQuadratic h).polarBilin (g e v) a=ell e v a) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+b+jointCompressionRank p f (2*f+b) := by
  classical
  let K (e : Comp p.g):=frozenChannelKernel h (P e) (C e) (g₀ e)
  have hK (e : Comp p.g) : K e≤P e:=frozen_channel_kernel_le h (P e) (C e) (g₀ e)
  let G:=(jointMatrixFunctional (M+B)).comp (jointXspace).subtype
  have hG (x : jointXspace) (hx : x.val∈jointQuadraticConstraints P K) : G x=0 := by
    change jointMatrixFunctional (M+B) x.val=0
    rw [joint_matrix_functional_add,hobs x.val x.property hx,char_two]
  obtain ⟨Z,hZ,hZv,hZr⟩:=joint_quadratic_target_solvable P K G hG
  have hQval (e : Comp p.g) (v : JointRay p n) (hv : v∈P e) :
      ((Z+B) e).toQuadraticForm' v=(B e).toQuadraticForm' v := by
    simp only [Pi.add_apply,matrix_quadratic_add,hZv e v hv,zero_add]
  have hQrow (e : Comp p.g) (k : JointRay p n) (hk : k∈K e) (v : JointRay p n) :
      ((Z+B) e).toQuadraticForm'.polarBilin k v=(B e).toQuadraticForm'.polarBilin k v := by
    simp only [Pi.add_apply,matrix_polar_add,hZr e k hk v,zero_add]
  have hQobs (x : JointProfile p n) (hx : x∈jointXspace) :
      jointMatrixFunctional (Z+B) x=jointMatrixFunctional M x := by
    have hz:=hZ ⟨x,hx⟩
    change jointMatrixFunctional Z x=jointMatrixFunctional (M+B) x at hz
    rw [joint_matrix_functional_add,hz,joint_matrix_functional_add,add_assoc,char_two,add_zero]
  obtain ⟨Q,hQv,hQr,hQo,hQrank⟩:=joint_quadratic_bounded_target P K M B (Z+B)
    f b r hP hK hM hB hQval hQrow hQobs
  have hreal (e : Comp p.g) := coordinate_quadratic_extension h (Q e) (P e) (C e) (g₀ e) (ell e)
    (fun v=>(hQv e v v.property).trans (hval e v)) (hcompat e)
    (fun v hv w=>(hQr e v (frozen_channel_kernel_mem h (P e) (C e) (g₀ e) v hv) w).trans
      (hrow e v hv w))
    (show (Q e).rank+5*dim (C e)+6*dim (P e)+2≤h from
      (Nat.add_le_add_right (Nat.add_le_add
        (Nat.add_le_add (hQrank e)
          (Nat.mul_le_mul_left 5 (hC e))) (Nat.mul_le_mul_left 6 (hP e))) 2).trans hroom)
  choose g hg hv hp using hreal
  exact ⟨Q,g,hg,hv,hp,hQo,hQrank⟩


end
end Lax793645Proofs.Simplifications
