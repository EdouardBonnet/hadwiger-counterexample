import Lax793645Proofs.Simplifications.OneFrameGeometry

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

instance oneFrameFintype (p : Shape) (n N : ℕ) : Fintype (OneFrame p n N) := by
  classical
  letI : Fintype (QuadraticFull (Ray p n) (Vec (Fin p.h))):=inferInstance
  letI : Fintype (Vec (HyperbolicIdx N)):=inferInstance
  exact Fintype.ofInjective (fun f : OneFrame p n N=>⇑f) DFunLike.coe_injective

instance oneOrientFintype (p : Shape) (n N : ℕ) : Fintype (OneOrient p n N) :=
  inferInstanceAs (Fintype (Comp p.g→OneFrame p n N))

/-- The new raw law samples independent, uniformly distributed single frames
at the cycle components. The own X-channel constraints are part of its support. -/
def oneRaw (m : Mixer p n) (N : ℕ) : Wgt (OneOrient p n N) := by
  classical
  exact prodW (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
    (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')

theorem one_frame_room (hN : Fintype.card (Row p n)+2*p.h+1≤N) :
    2*(Module.finrank F (Ray p n)+2*Module.finrank F (Vec (Fin p.h)))+2≤
      Module.finrank F (Vec (HyperbolicIdx N)) := by
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_fin,Fintype.card_sum]
  omega

theorem one_raw_law (m : Mixer p n) (hN : Fintype.card (Row p n)+2*p.h+1≤N) :
    IsLaw (oneRaw m N) := by
  classical
  apply prodW_law
  intro e
  exact quadratic_channel_raw_law _ (hyperbolic_matrix_nondegenerate N) _
    (one_frame_room hN)

theorem one_raw_nonneg (m : Mixer p n) (o : OneOrient p n N) : 0≤oneRaw m N o := by
  classical
  exact prodW_nonneg (fun _ _=>(unifOn_sub _).nz _) _

theorem one_raw_carried (m : Mixer p n) (N : ℕ) : carried (oneRaw m N) (oneFrameLaw m) := by
  classical
  intro o ho
  obtain ⟨e,he⟩:=not_forall.mp ho
  unfold oneRaw prodW
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  exact unifOn_carried _ _ he

/-- Exact quadratic-Gram observation for an independent nominal batch. -/
theorem one_frame_primal_observe {R : Type} [AddCommGroup R] [Module F R]
    [FiniteDimensional F R] [Fintype (R→ₗ[F]Vec (HyperbolicIdx N))]
    (m : Mixer p n) (J : R→ₗ[F]Ray p n) (hJ : Function.Injective J)
    (hN : Fintype.card (Row p n)+2*p.h+1≤N)
    (hR : Module.finrank F R+3≤N) :
    mapW (quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
      (fun P=> (onePrimal P).comp J)=
    unifOn (quadraticGramGood (hyperbolicMatrix N).toQuadraticForm'
      ((selfM p n m.mixM).toQuadraticForm'.comp J)) := by
  classical
  apply quadratic_channel_primal_observe _ (hyperbolic_matrix_nondegenerate N)
    _ J hJ (one_frame_room hN)
  change Module.finrank QField R+3≤N at hR
  simp only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_sum,Fintype.card_fin]
  omega

end
end Lax793645Proofs.Simplifications
