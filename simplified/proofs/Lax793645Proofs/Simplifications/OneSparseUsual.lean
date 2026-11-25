import Lax793645Proofs.Simplifications.OneCommonImageRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Matrix LinearMap
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem one_column_size (p : Shape) (n : ℕ) :
    num (OneColumn p n)=2*num (Row p n)+4*p.h := by
  have hd:=(oneEndpointCoordinates p n).finrank_eq
  change dim (Vec (OneColumn p n))=dim (Bool→OneFull p n) at hd
  rw [dim_vec] at hd
  have he : dim (Bool→OneFull p n)=dim (OneFull p n)+dim (OneFull p n) := by
    simp only [dim,Module.finrank_pi_fintype,Fintype.sum_bool]
  rw [he,one_full_dimension] at hd
  unfold num
  have hd' : Fintype.card (OneColumn p n)=2*Fintype.card (Row p n)+4*p.h:=by omega
  exact_mod_cast hd'

/-- The common-image rank cutoff is exponentially likely for every
law under the joint cap. The ambient dimension here is `2*N`. -/
theorem one_sparse_usual (p : Shape) (D : ℕ) (hd : 0<D) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m : Mixer p n) (w : Wgt (OneUnit p n N)),
        (∀ x,w x≤bp ((D:ℝ)*(2*N))*oneUnitRaw m N x) →
        pr w (fun x=>2*D<oneJoins x)≤bp (-(D:ℝ)/2*(2*N)) := by
  let a:=num (Comp p.g)*8*D
  have hA:=columns_budget p (δ:=(D:ℝ)/2) (by positivity) a 0
    (by unfold a num; positivity) (by norm_num)
  filter_upwards [one_raw_image_calendar p (ζ:=1/8) (by norm_num) (by norm_num),hA]
    with M hraw hcols
  filter_upwards [hraw,eventually_ge_atTop 1] with n hr hn
  intro N m w hw
  have hcols:=hcols n hn
  rw [add_zero] at hcols
  change a*num (Full p n)≤(D:ℝ)/2*N at hcols
  have hF : num (Full p n)=num (Row p n)+p.h:=by simp [num,Full]
  have hcost : num (Comp p.g)*num (OneColumn p n)*(2*D)≤(D:ℝ)/2*N := by
    rw [one_column_size]
    rw [hF] at hcols
    unfold a at hcols
    have hg : 0≤num (Comp p.g):=by unfold num; positivity
    have hrow : 0≤num (Row p n):=by unfold num; positivity
    have hh : 0≤(p.h:ℝ):=Nat.cast_nonneg _
    have hd0 : 0≤(D:ℝ):=Nat.cast_nonneg _
    have hm:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (show 2*num (Row p n)+4*p.h≤4*(num (Row p n)+p.h) by linarith only [hrow]) hg)
      (show 0≤2*(D:ℝ) by positivity)
    nlinarith only [hcols,hm]
  have hμ : ∀ x,0≤oneUnitRaw m N x:=prodW_nonneg (fun _=>one_raw_nonneg m)
  refine (pr_cap hw (fun x=>2*D<oneJoins x)).trans ?_
  have htail:=image_kernel_tail oneDualImages (oneUnitRaw m N) hμ (1/8)
    (by norm_num) (hr.2.2.2 m) (2*D)
  have hmono:=pr_mono hμ (p:=fun x=>2*D<oneJoins x)
    (q:=fun x=>2*D ≤ imageKernelRank oneDualImages x) (fun _ h=>h.le)
  refine (mul_le_mul_of_nonneg_left (hmono.trans htail) (bp_pos _).le).trans ?_
  rw [←bp_add]
  apply bp_le
  push_cast
  linarith only [hcost]

end
end Lax793645Proofs.Simplifications
