import Lax793645Proofs.Simplifications.OneScalarRecipes
import Lax793645Proofs.Simplifications.QuadraticChannelRealization
import Lax793645Proofs.Simplifications.QueryStatusWeights

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneCrossChannels (o : OneUnit p n N) (i : Bool) (e : Comp p.g) :
    Ray p n →ₗ[F] Hyperbolic p.h where
  toFun v:=(fun j=>(hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (oneChannelX (o (!i) e) j) (onePrimal (o i e) v),
    fun j=>(hyperbolicMatrix N).toQuadraticForm'.polarBilin
      (oneChannelY (o (!i) e) j) (onePrimal (o i e) v))
  map_add' v w:=by ext j <;> simp only [map_add,Pi.add_apply,Prod.fst_add,Prod.snd_add]
  map_smul' a v:=by ext j <;> simp only [map_smul,RingHom.id_apply] <;> rfl

/-- The new p-status is still a bounded-rank quadratic at every
orientation. A harmless factor two avoids choosing a special matrix
representative for the channel form. -/
theorem one_inner_gem (o : OneUnit p n N) (i : Bool) (t : Tag p.g) :
    ∃ M : Moment p n,M.rank ≤ tagDegree p.g*(2*p.h) ∧ ∀ s z,
      oneInner o i (atom p t s z)=mpair M (mom p s z) := by
  classical
  choose M hval hrank using (fun e=>hyperbolic_matrix_representative p.h (oneCrossChannels o i e))
  have hr e : (M e).rank ≤ 2*p.h := by
    refine (hrank e).trans ?_
    have hh : rk (oneCrossChannels o i e) ≤ Module.finrank F (Hyperbolic p.h):=
      Submodule.finrank_le _
    simpa only [Hyperbolic,Module.finrank_prod,dim_vec,Fintype.card_fin,two_mul] using hh
  let Z:=∑ e : TagStar t,M e.val
  refine ⟨Z,(mrk_sum_le ..).trans ((Finset.sum_le_sum (fun e _=>hr e.val)).trans_eq ?_),?_⟩
  · simp only [sum_const,card_univ,nsmul_eq_mul,card_star,Nat.cast_id]
  intro s z
  change (∑ e,quadraticChannelFunctional (hyperbolicMatrix N).toQuadraticForm'
    (oneChannelX (o (!i) e)) (oneChannelY (o (!i) e))
      (quadraticMomentMap (onePrimal (o i e)) (atom p t s z e)))=_
  have he e : quadraticChannelFunctional (hyperbolicMatrix N).toQuadraticForm'
      (oneChannelX (o (!i) e)) (oneChannelY (o (!i) e))
      (quadraticMomentMap (onePrimal (o i e)) (atom p t s z e))=
      if inc e t then mpair (M e) (mom p s z) else 0 := by
    rw [atom_def]
    by_cases ht : inc e t
    · rw [if_pos ht,if_pos ht,mom,quadratic_moment_outer,quadratic_channel_functional_outer,
        matrix_quadratic_outer,hval]
      rfl
    · simp only [ht,ite_false,map_zero]
  simp_rw [he]
  unfold Z
  rw [←Finset.sum_filter,mpair_sum]
  exact Finset.sum_subtype _ (by simp) _

variable {I : Type} [Fintype I] [DecidableEq I]

theorem one_inner_status_fourier (v : Template p I) (o : OneUnit p n N) (i : I)
    (φ : Wgt F) (hφ : ∀ a,|φ a| ≤ 1) :
    inputFourierNorm (fun x=>φ (oneInner o (v.aim i)
      (useAtom p (v.t i) (v.s i) (v.f i) (x i)))) ≤ bp ((tagDegree p.g*(2*p.h):ℕ):ℝ) := by
  obtain ⟨M,hM,he⟩:=one_inner_gem o (v.aim i) (v.t i)
  have hp x : oneInner o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i)
      (inputCoordinates p n I x i))=
      evmat M (inputRayLinear v i x+point p (v.s i) (0 : Base p.g n))
        (inputRayLinear v i x+point p (v.s i) (0 : Base p.g n)) := by
    rw [useAtom,he,mom,mpair_outer,input_ray_affine]
  unfold inputFourierNorm
  simp_rw [hp]
  exact (affine_quadratic_status_fourier M (inputRayLinear v i)
    (point p (v.s i) (0 : Base p.g n)) φ hφ).trans (bp_le (by exact_mod_cast hM))

def oneQueryPWeights (v : Template p I) (a : I → F) (o : OneUnit p n N) : Wgt (Inputs p n I):=
  fun x=>∏ i,ind (oneInner o (v.aim i) (useAtom p (v.t i) (v.s i) (v.f i) (x i))=a i)

theorem one_query_p_weights_norm (v : Template p I) (a : I → F) (o : OneUnit p n N) :
    inputFourierNorm (oneQueryPWeights v a o) ≤ bp (num I*(tagDegree p.g*(2*p.h):ℕ)) := by
  unfold inputFourierNorm oneQueryPWeights
  refine (fourier_norm_product _).trans ?_
  have hh i:=one_inner_status_fourier v o i (fun z=>ind (z=a i))
    (fun z=>by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _)
  refine (Finset.prod_le_prod (fun i _=>fourier_norm_nonneg _)
    (fun i _=>hh i)).trans_eq ?_
  rw [Finset.prod_const,Finset.card_univ,←bp_mul_nat]
  congr 1
  unfold num
  ring

theorem one_query_p_weights_indicator (v : Template p I) (a : I → F)
    (o : OneUnit p n N) (x : Inputs p n I) :
    oneQueryPWeights v a o x=ind (∀ i,oneInner o (v.aim i)
      (useAtom p (v.t i) (v.s i) (v.f i) (x i))=a i) := by
  exact (ind_all _).symm

end
end Lax793645Proofs.Simplifications
