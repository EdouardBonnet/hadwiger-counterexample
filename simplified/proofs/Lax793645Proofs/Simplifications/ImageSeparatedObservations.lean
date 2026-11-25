import Lax793645Proofs.Simplifications.ImageTupleBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] {N : ℕ}

def imageProbe (X : A→C→Mat (Fin N) I) {q t : C→ℕ}
    (B : ∀ e,Mat I (Fin (q e))) (D : ∀ e,Mat I (Fin (t e)))
    (Z : ImageTuple C q N) (T : ImageTuple C t N) (x : A) : Prop :=
  ∀ e,X x e*B e=Z e ∧X x e*D e=T e

/-- Observations on disjoint nominal blocks pay for their combined
rank, even when neither block is a stored coordinate block. -/
theorem image_probe_cap (X : A→C→Mat (Fin N) I) {q t : C→ℕ}
    (B : ∀ e,Mat I (Fin (q e))) (D : ∀ e,Mat I (Fin (t e)))
    (Z : ImageTuple C q N) (T : ImageTuple C t N)
    {w : Wgt A} (hw : ∀ x,0≤w x) {ζ : ℝ}
    (hcap : ∀ a : ImagePin C I N,pr w (imagePinAgree X a)≤fee N ζ (imagePlanRank a.sp))
    (hB : ∀ e,Function.Injective (B e).mulVec)
    (hD : ∀ e,Function.Injective (D e).mulVec)
    (hsep : ∀ e,Disjoint (colSp (B e)) (colSp (D e))) :
    pr w (imageProbe X B D Z T)≤fee N ζ ((∑ e,q e)+(∑ e,t e)) := by
  classical
  by_cases hp : 0<pr w (imageProbe X B D Z T)
  · obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw hp
    let P : ImagePlan C I:=fun e=>colSp (B e)⊔colSp (D e)
    let a : ImagePin C I N:=⟨P,X x⟩
    have he : pr w (imageProbe X B D Z T)≤pr w (imagePinAgree X a) := by
      apply pr_mono hw
      intro y hy e v hv
      obtain ⟨b,⟨u,rfl⟩,d,⟨v,rfl⟩,rfl⟩:=Submodule.mem_sup.mp hv
      change X y e*ᵥ(B e*ᵥu+D e*ᵥv)=X x e*ᵥ(B e*ᵥu+D e*ᵥv)
      rw [Matrix.mulVec_add,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,(hy e).1,(hx e).1,(hy e).2,(hx e).2]
    have hr : imagePlanRank a.sp=(∑ e,q e)+(∑ e,t e) := by
      change imagePlanRank ((fun e=>colSp (B e))⊔fun e=>colSp (D e))=_
      rw [image_plan_disjoint_rank _ _ hsep]
      congr 1 <;> apply Finset.sum_congr rfl
      · intro e _; exact (mrk_inj.mp (hB e)).trans (Fintype.card_fin _)
      · intro e _; exact (mrk_inj.mp (hD e)).trans (Fintype.card_fin _)
    exact he.trans (hr ▸ hcap a)
  exact (not_lt.mp hp).trans (bp_pos _).le

/-- Adaptive nominal coefficients can be enumerated before applying
the raw image bound; no conditioning on the observed value is used. -/
theorem image_probe_family_cap {J : Type} [Fintype J]
    (X : A→C→Mat (Fin N) I) {q t : C→ℕ}
    (B : J→∀ e,Mat I (Fin (q e))) (D : J→∀ e,Mat I (Fin (t e)))
    (Z : ImageTuple C q N) (T : ImageTuple C t N)
    {w : Wgt A} (hw : ∀ x,0≤w x) {ζ : ℝ}
    (hcap : ∀ a : ImagePin C I N,pr w (imagePinAgree X a)≤fee N ζ (imagePlanRank a.sp))
    (E : A→Prop)
    (hE : ∀ x,E x→∃ j,(∀ e,Function.Injective (B j e).mulVec ∧
      Function.Injective (D j e).mulVec ∧Disjoint (colSp (B j e)) (colSp (D j e))) ∧
      imageProbe X (B j) (D j) Z T x) :
    pr w E≤num J*fee N ζ ((∑ e,q e)+(∑ e,t e)) := by
  classical
  let P (j : J) (x : A):=(∀ e,Function.Injective (B j e).mulVec ∧
      Function.Injective (D j e).mulVec ∧Disjoint (colSp (B j e)) (colSp (D j e))) ∧
      imageProbe X (B j) (D j) Z T x
  apply ((pr_mono hw hE).trans (pr_exists_le hw P)).trans
  have hh (j) : pr w (P j)≤fee N ζ ((∑ e,q e)+(∑ e,t e)) := by
    by_cases hj : ∀ e,Function.Injective (B j e).mulVec ∧
      Function.Injective (D j e).mulVec ∧Disjoint (colSp (B j e)) (colSp (D j e))
    · exact (pr_mono hw (fun _ h=>h.2)).trans
        (image_probe_cap X (B j) (D j) Z T hw hcap
          (fun e=>(hj e).1) (fun e=>(hj e).2.1) (fun e=>(hj e).2.2))
    have he : P j=(fun _=>False):=funext (fun _=>propext (iff_false_intro (fun h=>hj h.1)))
    rw [he,pr_false]
    exact (bp_pos _).le
  exact (Finset.sum_le_sum (fun j _=>hh j)).trans_eq (by simp [num])

end
end Lax793645Proofs.Simplifications
