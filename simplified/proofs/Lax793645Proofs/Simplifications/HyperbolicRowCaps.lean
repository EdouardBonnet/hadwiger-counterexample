import Lax793645Proofs.Simplifications.QuadraticPolarRows
import Lax793645Proofs.Simplifications.QuadraticImageCaps

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem hyperbolic_nonzero_sphere (N : ℕ) (hN : 2≤N) (a : F) :
    (1/8:ℝ)≤pr unif (fun z : Vec (HyperbolicIdx N)=>
      z≠0 ∧ (hyperbolicMatrix N).toQuadraticForm' z=a) := by
  classical
  let q:=(hyperbolicMatrix N).toQuadraticForm'
  have hg : avg unif (fun z : Vec (HyperbolicIdx N)=>wsign (q z))=bp (-(N:ℝ)) := by
    simp only [q,hyperbolic_matrix_apply]
    have hh:=mapW_avg unif (hyperbolicCoordinates N).toEquiv
      (fun z=>wsign (hyperbolicQuadratic N z))
    rw [unif_equiv] at hh
    exact hh.symm.trans (hyperbolic_gauss N)
  have hbit (v : F) : ind (v=a)=(1+wsign v*wsign a)/2 := by
    rcases bit_cases v with rfl|rfl <;> rcases bit_cases a with rfl|rfl <;>
      norm_num [ind,wsign]
  have hm : pr unif (fun z : Vec (HyperbolicIdx N)=>q z=a)=
      (1+bp (-(N:ℝ))*wsign a)/2 := by
    unfold pr
    simp_rw [hbit]
    rw [avg_div,avg_add,unif_law.avg_const,avg_mul,hg]
  have hsmall : bp (-(N:ℝ))≤(1/4:ℝ) := by
    calc
      _≤bp (-2):=bp_le (by
        have hn : (2:ℝ)≤N:=by exact_mod_cast hN
        linarith only [hn])
      _=_:=by norm_num [bp]
  have hmass : (1/4:ℝ)≤pr unif (fun z : Vec (HyperbolicIdx N)=>q z=a) := by
    rw [hm]
    have hs : -(1:ℝ)≤wsign a:=(abs_le.mp (wsign_abs a).le).1
    have hh:=mul_le_mul_of_nonneg_left hs (bp_pos (-(N:ℝ))).le
    nlinarith only [hh,hsmall]
  have hzero : pr unif (fun z : Vec (HyperbolicIdx N)=>z=0)≤(1/8:ℝ) := by
    rw [pr_point',unif_apply,card_space,←bp_neg]
    have hd : dim (Vec (HyperbolicIdx N))=2*N:=by simp [dim_vec,HyperbolicIdx,two_mul]
    rw [hd]
    calc
      _≤bp (-3):=bp_le (by
        push_cast
        have hn : (2:ℝ)≤N:=by exact_mod_cast hN
        linarith only [hn])
      _=_:=by norm_num [bp]
  have hh:=pr_shield unif_law.nz (fun z : Vec (HyperbolicIdx N)=>q z=a) (fun z=>z≠0)
  simp only [not_not] at hh
  have he : pr unif (fun z : Vec (HyperbolicIdx N)=>q z=a ∧ z≠0)=
      pr unif (fun z : Vec (HyperbolicIdx N)=>z≠0 ∧ q z=a) := by
    congr 1
    funext z
    exact propext and_comm
  rw [he] at hh
  linarith only [hmass,hzero,hh]

variable {B R : Type} [AddCommGroup B] [Module F B]
  [AddCommGroup R] [Module F R] [FiniteDimensional F R]
  {N : ℕ} [Fintype (B→ₗ[F]Vec (HyperbolicIdx N))] [Fintype (Module.Dual F R)]

/-- Uniform row restrictions of the actual hyperbolic frame law. Unlike
a general capped leaf, its prepared marginal can afford this bound. -/
theorem hyperbolic_frame_row_cap (C : QuadraticForm F B→Prop)
    (J : R→ₗ[F]B) (hJ : Injective J) (θ : Module.Dual F R)
    (t : Vec (HyperbolicIdx N)) (ht : t≠0) (hN : 4≤N) :
    pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C))
      (fun P=>quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J) t=θ)≤
      8*bp (-(dim R:ℝ)) := by
  have hd : dim (Vec (HyperbolicIdx N))=2*N:=by simp [dim_vec,HyperbolicIdx,two_mul]
  simpa only [one_div,inv_inv] using quadratic_frame_row_cap
    (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
    C J hJ θ t ht (by rw [hd]; omega) (by norm_num : (0:ℝ)<1/8)
    (hyperbolic_nonzero_sphere N (by omega) _)

end
end Lax793645Proofs.Simplifications
