import Lax793645Proofs.Simplifications.ClosedImagePeeling

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I J : Type} [Fintype I] [Fintype J] {V : J→Type}
  [∀ j,AddCommGroup (V j)] [∀ j,Module F (V j)] [∀ j,FiniteDimensional F (V j)]

def coordinateClosure (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) : Space (Vec I) :=
  (blockClosure (P.map E.toLinearMap)).map E.symm.toLinearMap

theorem coordinate_closure_map (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    (coordinateClosure E P).map E.toLinearMap=blockClosure (P.map E.toLinearMap) := by
  rw [coordinateClosure,←Submodule.map_comp]
  simp

theorem le_coordinate_closure (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    P≤coordinateClosure E P := by
  intro v hv
  exact ⟨E v,le_blockClosure _ ⟨v,hv,rfl⟩,E.symm_apply_apply v⟩

theorem coordinate_closure_idempotent (E : Vec I≃ₗ[F](∀ j,V j)) (P : Space (Vec I)) :
    coordinateClosure E (coordinateClosure E P)=coordinateClosure E P := by
  change (blockClosure ((coordinateClosure E P).map E.toLinearMap)).map E.symm.toLinearMap=_
  rw [coordinate_closure_map,blockClosure_idempotent]
  rfl

theorem coordinate_closure_growth (E : Vec I≃ₗ[F](∀ j,V j)) (P Q : Space (Vec I))
    (hPQ : P≤Q) (hP : coordinateClosure E P=P) :
    dim (coordinateClosure E Q)-dim P≤Fintype.card J*(dim Q-dim P) := by
  have hp : blockClosure (P.map E.toLinearMap)=P.map E.toLinearMap :=
    (coordinate_closure_map E P).symm.trans (congrArg (Submodule.map E.toLinearMap) hP)
  have h:=blockClosure_dimension_step (P.map E.toLinearMap) (Q.map E.toLinearMap)
    (Submodule.map_mono hPQ) hp
  have he : dim (coordinateClosure E Q)=dim (blockClosure (Q.map E.toLinearMap)):=
    E.symm.finrank_map_eq _
  change dim (blockClosure (Q.map E.toLinearMap))-dim (P.map E.toLinearMap)≤
    Fintype.card J*(dim (Q.map E.toLinearMap)-dim (P.map E.toLinearMap)) at h
  rw [he]
  simpa only [dim,LinearEquiv.finrank_map_eq] using h

variable {C : Type} [Fintype C]

/-- Closing every component under the same coordinate blocks has the
same closure factor; the number of components does not inflate it. -/
def coordinateImageClosure (E : Vec I≃ₗ[F](∀ j,V j)) : ImageClosure C I (Fintype.card J) where
  close P e:=coordinateClosure E (P e)
  extensive P e:=le_coordinate_closure E (P e)
  idempotent P:=funext (fun e=>coordinate_closure_idempotent E (P e))
  growth P Q hPQ hP:=by
    have hg (e : C) : dim (coordinateClosure E (Q e))≤
        dim (P e)+Fintype.card J*(dim (Q e)-dim (P e)) := by
      have h:=coordinate_closure_growth E (P e) (Q e) (hPQ e) (congrFun hP e)
      omega
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>hg e)
    rw [Finset.sum_add_distrib,←Finset.mul_sum] at hh
    have hd : (∑ e,(dim (Q e)-dim (P e)))=imagePlanRank Q-imagePlanRank P := by
      rw [imagePlanRank,imagePlanRank,Finset.sum_tsub_distrib]
      exact fun e _=>Submodule.finrank_mono (hPQ e)
    rw [hd] at hh
    change imagePlanRank (fun e=>coordinateClosure E (Q e))≤
      imagePlanRank P+Fintype.card J*(imagePlanRank Q-imagePlanRank P) at hh
    omega

end
end Lax793645Proofs.Simplifications
