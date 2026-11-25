import Lax793645Proofs.Simplifications.QuadraticObservationBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrix_quadratic_comp {I A : Type} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] (E : Mat A A) (P : Vec I→ₗ[F]Vec A) :
    E.toQuadraticForm'.comp P=
      (pullM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E).toQuadraticForm' := by
  apply QuadraticMap.ext
  intro x
  change Matrix.toBilin' E (P x) (P x)=
    Matrix.toBilin' (pullM (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E) x x
  simp only [Matrix.toBilin'_apply']
  simpa only [evmat,LinearMap.toMatrix'_mulVec] using
    (evmat_pull (LinearMap.toMatrix' P) (LinearMap.toMatrix' P) E x x).symm

variable {I : Type} [Fintype I] [DecidableEq I]

theorem quadratic_gram_weight_bound (N : ℕ)
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))]
    (M : Mat I I) (hN : 2*num I+2≤N) (T : Vec I→ₗ[F]Vec (HyperbolicIdx N)) :
    unifOn (quadraticGramGood (hyperbolicMatrix N).toQuadraticForm' M.toQuadraticForm') T≤
      bp ((num I)^2+2-2*N*num I) := by
  have hn:=quadratic_gram_lower N M hN
  have hc:=on_mon unif_subLaw.nz (bp_pos (-(num I)^2-2)) hn T
  rw [on_unif] at hc
  refine hc.trans_eq ?_
  rw [unif_apply,card_space,←bp_neg,←bp_neg,←bp_add]
  apply congrArg bp
  have hd : (dim (Vec I→ₗ[F]Vec (HyperbolicIdx N)):ℝ)=num I*(2*N) := by
    simp only [dim,Module.finrank_linearMap,Module.finrank_pi_fintype,Module.finrank_self,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_sum,Fintype.card_fin]
    push_cast
    unfold num
    ring
  rw [hd]
  ring

/-- A fixed t-dimensional image costs 2^{-t(2N-t)+2}, uniformly in the
quadratic data imposed on the full frame. N is half the ambient dimension. -/
theorem quadratic_image_cap {B : Type} [AddCommGroup B] [Module F B]
    [FiniteDimensional F B] (N : ℕ)
    [Fintype (B→ₗ[F]Vec (HyperbolicIdx N))]
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))]
    (C : QuadraticForm F B→Prop)
    (hc : ∃ P,quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C P)
    (J : Vec I→ₗ[F]B) (hJ : Function.Injective J)
    (hN : 2*num I+3≤N) (T : Vec I→ₗ[F]Vec (HyperbolicIdx N)) :
    pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C))
      (fun P=>P.comp J=T)≤bp ((num I)^2+2-2*N*num I) := by
  have hn : 2*Fintype.card I+3≤N := by exact_mod_cast hN
  have hroom : 2*Module.finrank QField (Vec I)+6≤
      Module.finrank QField (Vec (HyperbolicIdx N)) := by
    simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_sum,Fintype.card_fin]
    omega
  have hbound:=quadratic_frames_observation_cap _ (hyperbolic_matrix_nondegenerate N)
    C hc J hJ hroom T
  rw [matrix_quadratic_comp] at hbound
  exact hbound.trans (quadratic_gram_weight_bound N _ (by linarith) T)

end
end Lax793645Proofs.Simplifications
