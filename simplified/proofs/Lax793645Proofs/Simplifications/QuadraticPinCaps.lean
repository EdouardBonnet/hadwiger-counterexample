import Lax793645Proofs.Simplifications.QuadraticImageCaps
import Lax793645Proofs.Simplifications.OneFrameLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [AddCommGroup B] [Module F B] [FiniteDimensional F B]

/-- The raw quadratic-frame cap applies to an actual stored subspace,
with no assumption that its vectors lie in a single coordinate block. -/
theorem quadratic_pin_cap (N : ℕ) [Fintype (B→ₗ[F]Vec (HyperbolicIdx N))]
    (C : QuadraticForm F B→Prop)
    (hc : ∃ P,quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C P)
    (P : Space B) (T : B→ₗ[F]Vec (HyperbolicIdx N)) (hN : 2*dim P+3≤N) :
    pr (unifOn (quadraticFramesAt (hyperbolicMatrix N).toQuadraticForm' C))
      (fun g=>∀ v∈P,g v=T v)≤bp ((dim P:ℝ)^2+2-2*N*dim P) := by
  classical
  let E:=(Module.finBasis F P).equivFun
  let J : Vec (Fin (dim P))→ₗ[F]B:=P.subtype.comp E.symm.toLinearMap
  have hJ : Function.Injective J:=P.subtype_injective.comp E.symm.injective
  have hh (g : B→ₗ[F]Vec (HyperbolicIdx N)) :
      (∀ v∈P,g v=T v)↔g.comp J=T.comp J := by
    constructor
    · intro h
      apply LinearMap.ext
      intro v
      exact h _ (E.symm v).property
    · intro h v hv
      have he:=LinearMap.congr_fun h (E ⟨v,hv⟩)
      simpa only [J,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,
        Submodule.subtype_apply] using he
  have he : (fun g : B→ₗ[F]Vec (HyperbolicIdx N)=>∀ v∈P,g v=T v)=
      (fun g=>g.comp J=T.comp J):=funext (fun g=>propext (hh g))
  rw [he]
  letI : Fintype (Vec (Fin (dim P))→ₗ[F]Vec (HyperbolicIdx N)):=
    Fintype.ofInjective (fun f : Vec (Fin (dim P))→ₗ[F]Vec (HyperbolicIdx N)=>⇑f)
      DFunLike.coe_injective
  have hn : 2*num (Fin (dim P))+3≤N := by
    simpa only [num,Fintype.card_fin] using (show (2*(dim P:ℝ)+3:ℝ)≤N by exact_mod_cast hN)
  simpa only [num,Fintype.card_fin] using quadratic_image_cap N C hc J hJ hn (T.comp J)

variable {p : Shape} {n N : ℕ}

theorem one_frame_pin_cap (m : Mixer p n)
    (P : Space (QuadraticFull (Ray p n) (Vec (Fin p.h))))
    (T : OneFrame p n N) (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hN : 2*dim P+3≤N) :
    pr (quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
      (selfM p n m.mixM).toQuadraticForm') (fun g=>∀ v∈P,g v=T v)≤
      bp ((dim P:ℝ)^2+2-2*N*dim P) := by
  apply quadratic_pin_cap N (quadraticChannelClass _) _ P T hN
  exact quadratic_channel_frames_exist _ (hyperbolic_matrix_nondegenerate N) _
    (one_frame_room hroom)

end
end Lax793645Proofs.Simplifications
