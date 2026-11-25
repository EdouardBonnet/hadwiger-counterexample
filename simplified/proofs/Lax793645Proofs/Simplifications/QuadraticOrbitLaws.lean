import Lax793645Proofs.Simplifications.QuadraticFrameMoves
import Lax793645Proofs.Simplifications.QuadraticFrameSymmetry
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteConditioning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B R V : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup R] [Module QField R] [AddCommGroup V] [Module QField V]

def quadraticFramesAt (q : QuadraticForm QField V) (C : QuadraticForm QField B→Prop)
    (P : B→ₗ[QField]V) := Function.Injective P ∧ C (q.comp P)

def quadraticGramGood (q : QuadraticForm QField V) (Q : QuadraticForm QField B)
    (P : B→ₗ[QField]V) := quadraticFramesAt q (fun A=>A=Q) P

def quadraticPost (q : QuadraticForm QField V) (e : q.IsometryEquiv q) :
    (B→ₗ[QField]V)≃(B→ₗ[QField]V) where
  toFun P:=e.toLinearEquiv.toLinearMap.comp P
  invFun P:=e.symm.toLinearEquiv.toLinearMap.comp P
  left_inv P:=by ext x; exact e.symm_apply_apply _
  right_inv P:=by ext x; exact e.apply_symm_apply _

theorem quadratic_post_form (q : QuadraticForm QField V) (e : q.IsometryEquiv q)
    (P : B→ₗ[QField]V) : q.comp (quadraticPost q e P)=q.comp P := by
  apply QuadraticMap.ext
  intro x
  exact e.map_app _

theorem quadratic_post_invar (q : QuadraticForm QField V) (e : q.IsometryEquiv q)
    (C : QuadraticForm QField B→Prop) (P : B→ₗ[QField]V) :
    quadraticFramesAt q C P ↔ quadraticFramesAt q C (quadraticPost q e P) := by
  rw [quadraticFramesAt,quadraticFramesAt,quadratic_post_form]
  apply and_congr_left
  intro _
  exact ⟨fun h=>e.injective.comp h,fun h=>fun x y hxy=>h (congrArg e hxy)⟩

/-- Any feasible nominal quadratic form has frames in a sufficiently large
nondegenerate ambient quadratic space. -/
theorem quadratic_frames_exists [FiniteDimensional QField B] [FiniteDimensional QField V]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (C : QuadraticForm QField B→Prop) (hC : ∃ Q,C Q)
    (hroom : 2*Module.finrank QField B+2≤Module.finrank QField V) :
    ∃ P : B→ₗ[QField]V,quadraticFramesAt q C P := by
  obtain ⟨Q,hQ⟩:=hC
  obtain ⟨P,hP,hq,_⟩:=quadratic_embedding_extension Q q hnd hroom ⊥ 0
    (fun _ _ _=>Subsingleton.elim _ _) (by
      intro s
      have hs : (s:B)=0:=s.property
      simp only [LinearMap.zero_apply,hs,map_zero])
  have he : q.comp P=Q:=QuadraticMap.ext (fun x=>hq x)
  exact ⟨P,hP,he.symm ▸ hQ⟩

/-- Restricting a uniformly sampled quadratic frame gives the exact uniform
law with the prescribed restricted quadratic Gram data. -/
theorem quadratic_frames_observe [FiniteDimensional QField R] [FiniteDimensional QField V]
    [Fintype (B→ₗ[QField]V)] [Fintype (R→ₗ[QField]V)]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (C : QuadraticForm QField B→Prop)
    (hc : ∃ P : B→ₗ[QField]V,quadraticFramesAt q C P)
    (J : R→ₗ[QField]B) (hJ : Function.Injective J) (Q : QuadraticForm QField R)
    (hQ : ∀ A,C A → A.comp J=Q)
    (hroom : 2*Module.finrank QField R+6≤Module.finrank QField V) :
    mapW (unifOn (quadraticFramesAt q C)) (fun P=>P.comp J)=
      unifOn (quadraticGramGood q Q) := by
  apply uniform_orbit _ hc
  · intro P hP
    exact ⟨hP.1.comp hJ,hQ _ hP.2⟩
  · intro y z hy hz
    obtain ⟨e,he⟩:=quadratic_frame_symmetry q hnd y z hy.1 hz.1
      (fun x=>congrArg (fun A : QuadraticForm QField R=>A x) (hy.2.trans hz.2.symm))
    refine ⟨quadraticPost q e,quadratic_post_invar q e C,fun P=>?_⟩
    have he' : quadraticPost q e y=z:=LinearMap.ext he
    have hobs : (quadraticPost q e P).comp J=quadraticPost q e (P.comp J) := rfl
    rw [hobs,←he']
    exact (quadraticPost q e).injective.eq_iff.symm

end
end Lax793645Proofs.Simplifications
