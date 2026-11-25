import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteAffineLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Z V W : Type} [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

theorem linear_dual_deficit (L : V→ₗ[F]W) (A : Z→ₗ[F]V) :
    rk (L.comp A)+dim ((A.dualMap.comp L.rangeRestrict.dualMap).ker)=rk L := by
  let f:=L.rangeRestrict.comp A
  have he : (L.comp A).ker=f.ker := by
    ext z
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg Subtype.val h
  have hf:=f.finrank_range_add_finrank_ker
  have hg:=(L.comp A).finrank_range_add_finrank_ker
  have hr : rk (L.comp A)=rk f := by
    change finrank F (L.comp A).range=finrank F f.range
    rw [he] at hg
    omega
  have hd:=f.dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,Subspace.dual_finrank_eq] at hd
  rw [hr]
  rw [LinearMap.dualMap_comp_dualMap]
  exact hd

/-- A rank loss of at most d multiplies every affine cell probability
by at most 2^d. No bound on the number of defining rows enters this factor. -/
theorem linear_affine_cell_cap [Fintype Z] [Fintype V] [Fintype W]
    (L : V→ₗ[F]W) (A : Z→ₗ[F]V) (d : ℕ)
    (hd : dim ((A.dualMap.comp L.rangeRestrict.dualMap).ker)≤d)
    (b : V) (w : W) :
    pr unif (fun z : Z=>L (A z+b)=w)≤bp (d:ℝ)*mapW unif L w := by
  by_cases hw : w∈L.range
  · have he (z : Z) : L (A z+b)=w↔(L.comp A) z=w-L b:=by
      rw [map_add,eq_sub_iff_add_eq]
      rfl
    simp_rw [he]
    rw [pr_unif_lin]
    have hr : mapW unif L w=bp (-(rk L:ℝ)):=by
      change pr unif (fun x=>L x=w)=_
      rw [pr_unif_lin,ind_one hw,one_mul]
    rw [hr,←bp_add]
    refine ((mul_le_mul_of_nonneg_right (ind_le_one _) (bp_pos _).le).trans_eq
      (one_mul _)).trans ?_
    apply bp_le
    have hdim:=linear_dual_deficit L A
    have hnat : rk L≤rk (L.comp A)+d:=by omega
    have hh : (rk L:ℝ)≤rk (L.comp A)+d:=by exact_mod_cast hnat
    linarith only [hh]
  · have hfalse (z : Z) : ¬L (A z+b)=w:=fun h=>hw ⟨A z+b,h⟩
    simp only [pr,ind_zero (hfalse _),avg_zero]
    exact mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz)

theorem uniform_translate_average {U : Type} [AddCommGroup U] [Fintype U]
    (f : Wgt U) (z : U) : avg unif (fun x=>f (x+z))=avg unif f := by
  have h:=avg_bij (Equiv.addRight z) (unif : Wgt U) f
  simpa only [avg,unif_apply,Equiv.coe_addRight] using h

theorem uniform_free_cell_cap {U : Type} [AddCommGroup U] [Fintype U]
    [Fintype Z] [Fintype V] [Fintype W]
    (K : U→V) (J : Z→U) (A : Z→ₗ[F]V)
    (hK : ∀ x z,K (x+J z)=A z+K x)
    (L : V→ₗ[F]W) (d : ℕ)
    (hd : dim ((A.dualMap.comp L.rangeRestrict.dualMap).ker)≤d) (w : W) :
    pr unif (fun x=>L (K x)=w)≤bp (d:ℝ)*mapW unif L w := by
  have he : pr unif (fun x=>L (K x)=w)=
      avg unif (fun x=>pr unif (fun z=>L (A z+K x)=w)) := by
    have ht (z : Z) : avg unif (fun x=>ind (L (K (x+J z))=w))=
        pr unif (fun x=>L (K x)=w):=
      uniform_translate_average (fun x=>ind (L (K x)=w)) (J z)
    have hh : pr unif (fun x=>L (K x)=w)=avg unif
        (fun z : Z=>avg unif (fun x=>ind (L (K (x+J z))=w))) := by
      simp_rw [ht]
      exact ((unif_law (α:=Z)).avg_const _).symm
    rw [hh,avg_avg]
    simp only [hK,pr]
  rw [he]
  exact unif_law.avg_le (fun x=>linear_affine_cell_cap L A d hd (K x) w)

end
end Lax793645Proofs.Simplifications
