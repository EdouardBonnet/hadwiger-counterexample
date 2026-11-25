import Lax793645Proofs.Simplifications.QuadraticMultiRowBounds
import Lax793645Proofs.Simplifications.OnePreparedLinearRank

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N d : ℕ}

theorem one_independent_rows (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 2*d+3≤N)
    (J : Vec (Fin n)→ₗ[F]OneFull p n) (hJ : Injective J)
    (T : Vec (Fin d)→ₗ[F](Comp p.g→Vec (HyperbolicIdx N)))
    (e : Comp p.g) (he : Injective ((LinearMap.proj e).comp T))
    (Θ : Vec (Fin d)→ₗ[F]Module.Dual F (Vec (Fin n))) :
    pr (oneRaw m N) (fun o=>(oneMixedRow J o).comp T=Θ)≤
      bp ((d:ℝ)^2+2-d*n) := by
  letI : Fintype (Module.Dual F (Vec (Fin n))):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  letI : Fintype (Vec (Fin d)→ₗ[F]Module.Dual F (Vec (Fin n))):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  letI : Fintype (Vec (Fin d)→ₗ[F]Vec (HyperbolicIdx N)):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  obtain ⟨P,hP⟩:=quadratic_channel_frames_exist (hyperbolicMatrix N).toQuadraticForm'
    (hyperbolic_matrix_nondegenerate N) (selfM p n m.mixM).toQuadraticForm'
    (C:=Vec (Fin p.h)) (one_frame_room hroom)
  let f (i : Comp p.g) (P : OneFrame p n N):=
    (quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J)).comp
      ((LinearMap.proj i).comp T)
  have hh:=independent_sum_point_cap
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law ⟨P,hP⟩) f e (bp ((d:ℝ)^2+2-d*n))
    (fun y=>by
      change pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm'
        (quadraticChannelClass (C:=Vec (Fin p.h)) (selfM p n m.mixM).toQuadraticForm')))
        (fun P=>(quadraticPolarRead (hyperbolicMatrix N).toQuadraticForm' (P.comp J)).comp
          ((LinearMap.proj e).comp T)=y)≤_
      simpa only [num,dim_vec,Fintype.card_fin] using hyperbolic_frame_rows_cap N
        (quadraticChannelClass (C:=Vec (Fin p.h)) (selfM p n m.mixM).toQuadraticForm')
        J hJ y ((LinearMap.proj e).comp T) he (by
          simp only [num,Fintype.card_fin]; exact_mod_cast hN)) Θ
  have hf (o : OneOrient p n N) : (∑ i,f i (o i))=(oneMixedRow J o).comp T := by
    ext x z
    simp only [f,oneMixedRow,LinearMap.sum_apply,LinearMap.comp_apply]
  simpa only [hf,oneRaw] using hh

end
end Lax793645Proofs.Simplifications
