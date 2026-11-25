import Lax793645Proofs.Simplifications.OneSymmetricOffsets
import Lax793645Proofs.Simplifications.OnePrimalImageBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

theorem one_primal_coordinates_separated (P : OneFrame p n N)
    (T : Space (Vec (Fin (2*N))))
    (h : Disjoint (LinearMap.range (onePrimal P))
      (T.map (oneAmbientCoordinates N).symm.toLinearMap)) :
    Disjoint (colSp (onePrimalMatrix P)) T := by
  rw [Submodule.disjoint_def] at h ⊢
  rintro x ⟨v,hv⟩ hx
  have he : oneAmbientCoordinates N (onePrimal P v)=x := by
    change onePrimalMatrix P*ᵥv=x at hv
    simpa only [onePrimalMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply,
      LinearEquiv.coe_coe] using hv
  have hz := h (onePrimal P v) ⟨v,rfl⟩
    ⟨x,hx,by rw [←he]; exact (oneAmbientCoordinates N).symm_apply_apply _⟩
  rw [←he,hz,map_zero]

theorem one_unit_cover_component {w : Wgt (OneUnit p n N)} {H : ℝ}
    (m : Mixer p n) (i : Bool) (hH : 0≤H) (hw : SubLaw w)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (e : Comp p.g) (T : Space (Vec (Fin (2*N)))) :
    pr w (fun x=>¬Disjoint (onePrimalImages x i e) T)≤
      H*bp (num (Row p n)+dim T+3-2*(N:ℝ)) := by
  let T' := T.map (oneAmbientCoordinates N).symm.toLinearMap
  let E (P : OneFrame p n N):=¬Disjoint (LinearMap.range (onePrimal P)) T'
  have ht : dim T'=dim T := (oneAmbientCoordinates N).symm.finrank_map_eq T
  have hc:=pr_cap (one_unit_component_cap m i hcap hroom e) E
  rw [mapW_pr] at hc
  refine (pr_mono hw.nz (fun x hx h=>hx (one_primal_coordinates_separated _ _ h))).trans
    (hc.trans ?_)
  rw [←ht]
  exact mul_le_mul_of_nonneg_left (one_primal_intersection_cap m hroom hN T') hH

end
end Lax793645Proofs.Simplifications
