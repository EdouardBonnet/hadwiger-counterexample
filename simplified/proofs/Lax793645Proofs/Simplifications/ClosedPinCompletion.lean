import Lax793645Proofs.Simplifications.ClosedBlockPins
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CoverSpaces

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]

/-- Completing an exact-image event from S to T costs only the new image
coordinates. The witness is an actual sampled image, so all retained pin
equations remain consistent. -/
theorem closed_pin_completion
    (w : Wgt A) (hw : ∀ x,0≤w x) (E : A→Prop) (N : ℕ)
    (X : A→Mat (Fin N) I) (S T : Space (Vec I)) (hST : S≤T)
    (hE : ∀ x,E x→∀ y,E y→∀ v∈S,X x*ᵥv=X y*ᵥv)
    (a : ℕ) (ha : a≤dim S) (c ζ : ℝ) (hc : 0<c) (hz : 0≤ζ)
    (hstep : ((dim T-a:ℕ):ℝ)≤c*(dim S-a:ℕ))
    (he : fee N ζ (dim S-a)<pr w E) :
    ∃ x₀,E x₀ ∧ fee N (ζ/c) (dim T-a)<
      pr w (fun x=>E x ∧ ∀ v∈T,X x*ᵥv=X x₀*ᵥv) := by
  classical
  let D:=chopSpace S T
  let V:=Mat (Fin N) (Fin (dim D))
  let f : A→V:=fun x=>X x*pack D
  have hd : dim D=dim T-dim S := by
    have h:=chopSpace_rank S T
    rw [sup_eq_right.mpr hST] at h
    change dim S+dim D=dim T at h
    omega
  have hdim : dim S≤dim T:=Submodule.finrank_mono hST
  have hu : dim S-a≤dim T-a:=Nat.sub_le_sub_right hdim a
  have hcount : num V≤bp ((((dim T-a)-(dim S-a):ℕ):ℝ)*N) := by
    have hu' : dim T-a-(dim S-a)=dim D:=by omega
    rw [hu']
    change (Fintype.card V:ℝ)≤_
    rw [card_space]
    apply bp_le
    have hv : dim V=N*dim D:=by
      change dim (Mat (Fin N) (Fin (dim D)))=N*dim D
      rw [dim_mat]
      simp
    rw [hv]
    push_cast
    exact le_of_eq (mul_comm _ _)
  obtain ⟨v,hv⟩:=closed_pin_step w hw E f N (dim S-a) (dim T-a) c ζ hc hz hu hstep hcount he
  obtain ⟨x₀,hx₀,_⟩:=exists_of_pr_pos hw ((bp_pos _).trans hv)
  refine ⟨x₀,hx₀.1,hv.trans_le (pr_mono hw ?_)⟩
  intro x hx
  refine ⟨hx.1,?_⟩
  intro v hv
  have hjoin : S⊔D=T:=(chopSpace_join S T).trans (sup_eq_right.mpr hST)
  rw [←hjoin] at hv
  obtain ⟨s,hs,d,hd',rfl⟩:=Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add,Matrix.mulVec_add,hE x hx.1 x₀ hx₀.1 s hs]
  congr 1
  obtain ⟨u,rfl⟩:=(pack_mem_iff d D).mp hd'
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  have hsame : X x*pack D=X x₀*pack D:=hx.2.trans hx₀.2.symm
  rw [hsame]

end
end Lax793645Proofs.Simplifications
