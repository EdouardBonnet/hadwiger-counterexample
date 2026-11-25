import Lax793645Proofs.Simplifications.OneChannelImageBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneRayLine (v : Ray p n) : Vec (Fin 1)→ₗ[F]OneFull p n :=
  (LinearMap.proj 0).smulRight (v,0)

theorem one_ray_line_injective {v : Ray p n} (hv : v≠0) :
    Function.Injective (oneRayLine v) := by
  intro a b he
  have h : a 0 • v=b 0 • v:=congrArg Prod.fst he
  have hh:=smul_left_injective F hv h
  funext j
  simpa only [show j=(0:Fin 1) from Subsingleton.elim _ _] using hh

/-- A nonzero primal vector has a uniformly small image atom under the
quadratic-frame law, regardless of its prescribed quadratic value. -/
theorem one_primal_point_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (v : Ray p n) (hv : v≠0) (t : Vec (HyperbolicIdx N)) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm') (fun P=>onePrimal P v=t)≤bp (3-2*(N:ℝ)) := by
  classical
  letI : Fintype (Vec (Fin 1)→ₗ[F]Vec (HyperbolicIdx N)):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  have hc:=quadratic_channel_frames_exist (hyperbolicMatrix N).toQuadraticForm'
    (hyperbolic_matrix_nondegenerate N) (selfM p n m.mixM).toQuadraticForm'
    (C:=Vec (Fin p.h)) (one_frame_room hroom)
  let T : Vec (Fin 1)→ₗ[F]Vec (HyperbolicIdx N):=(LinearMap.proj 0).smulRight t
  have hh:=quadratic_image_cap N (quadraticChannelClass (C:=Vec (Fin p.h))
    (selfM p n m.mixM).toQuadraticForm') hc (oneRayLine v) (one_ray_line_injective hv)
    (by norm_num [num]; exact_mod_cast hN) T
  refine (pr_mono (unifOn_sub _).nz (q:=fun P=>P.comp (oneRayLine v)=T) ?_).trans ?_
  · intro P hP
    apply LinearMap.ext
    intro a
    change P (a 0 • (v,0))=a 0 • t
    rw [map_smul]
    exact congrArg (a 0 • ·) hP
  · norm_num [num] at hh
    exact hh

/-- A fixed low-dimensional ambient space rarely meets a primal image.
The estimate is obtained by two finite unions, without group theory. -/
theorem one_primal_intersection_cap (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (T : Space (Vec (HyperbolicIdx N))) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm')
      (fun P=>¬Disjoint (LinearMap.range (onePrimal P)) T)≤
      bp (num (Row p n)+dim T+3-2*(N:ℝ)) := by
  classical
  let μ:=quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
    (selfM p n m.mixM).toQuadraticForm'
  have hμ : ∀ P,0≤μ P:=(unifOn_sub _).nz
  let C (v : Ray p n) (t : T) (P : OneFrame p n N):=v≠0 ∧ onePrimal P v=t.val
  have he (P) (hp : ¬Disjoint (LinearMap.range (onePrimal P)) T) : ∃ v,∃ t,C v t P := by
    rw [Submodule.disjoint_def] at hp
    push Not at hp
    obtain ⟨x,⟨v,hv⟩,ht,hx⟩:=hp
    refine ⟨v,⟨x,ht⟩,?_,hv⟩
    intro hz
    exact hx (hv.symm.trans (hz ▸ map_zero _))
  have hC (v : Ray p n) (t : T) : pr μ (C v t)≤bp (3-2*(N:ℝ)) := by
    by_cases hv : v=0
    · simp only [C,hv,ne_eq,not_true_eq_false,false_and,pr_false]
      exact (bp_pos _).le
    · simp only [C,hv,ne_eq,not_false_eq_true,true_and]
      exact one_primal_point_cap m hroom hN v hv t.val
  refine ((pr_mono hμ he).trans (pr_exists_le hμ _)).trans ?_
  refine (Finset.sum_le_sum fun v _=>(pr_exists_le hμ _).trans
    (Finset.sum_le_sum fun t _=>hC v t)).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [card_space,card_space,←mul_assoc,←bp_add,←bp_add]
  apply congrArg bp
  have hd : (dim (Ray p n):ℝ)=num (Row p n) := by
    change (dim (Vec (Row p n)):ℝ)=_
    simp [dim,Vec,num]
  rw [hd]
  ring

theorem one_primal_pair_intersection_cap (m : Mixer p n) (R : OneFrame p n N)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm')
      (fun P=>¬Disjoint (LinearMap.range (onePrimal P)) (LinearMap.range (onePrimal R)))≤
      bp (2*num (Row p n)+3-2*(N:ℝ)) := by
  refine (one_primal_intersection_cap m hroom hN _).trans (bp_le ?_)
  have hd : dim (LinearMap.range (onePrimal R))≤Fintype.card (Row p n) :=
    (LinearMap.finrank_range_le (onePrimal R)).trans_eq (dim_vec _)
  have hd' : (dim (LinearMap.range (onePrimal R)):ℝ)≤num (Row p n) := by exact_mod_cast hd
  linarith

end
end Lax793645Proofs.Simplifications
