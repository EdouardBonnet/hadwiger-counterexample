import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A conditional probability bound uniform over every fine fiber also
holds on every union of fibers. Zero-mass fibers require no choices. -/
theorem conditional_coarsening_bound {A B C : Type} [Fintype A] [Fintype B]
    (μ : Wgt A) (hμ : ∀ x,0≤μ x) (f : A→B) (g : B→C)
    (p : A→Prop) (R : ℝ) (hR : 0≤R)
    (h : ∀ b,pr (onW μ (fun x=>f x=b)) p≤R) (c : C) :
    pr (onW μ (fun x=>g (f x)=c)) p≤R := by
  have hf (b : B) : mapW (subW μ p) f b≤R*mapW μ f b := by
    change pr (subW μ p) (fun x=>f x=b)≤_
    rw [pr_sub]
    have he : (fun x=>p x ∧ f x=b)=(fun x=>f x=b ∧ p x) := by
      funext x
      exact propext and_comm
    rw [he,pr_of_on hμ]
    exact (mul_le_mul_of_nonneg_left (h b) (pr_nonneg hμ)).trans_eq (mul_comm _ _)
  have hh:=mapW_cap hf g c
  rw [mapW_nested,mapW_nested] at hh
  change pr (subW μ p) (fun x=>g (f x)=c)≤R*pr μ (fun x=>g (f x)=c) at hh
  rw [pr_sub] at hh
  have he : (fun x=>p x ∧ g (f x)=c)=(fun x=>g (f x)=c ∧ p x) := by
    funext x
    exact propext and_comm
  rw [he] at hh
  rw [pr_on]
  by_cases hz : pr μ (fun x=>g (f x)=c)=0
  · rw [hz,div_zero]
    exact hR
  · exact (div_le_iff₀ (lt_of_le_of_ne (pr_nonneg hμ) (Ne.symm hz))).mpr hh

end
end Lax793645Proofs.Simplifications
