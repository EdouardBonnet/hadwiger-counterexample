import Lax793645Proofs.Simplifications.LinearCellCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A : Type} [AddCommGroup V] [Module F V]

/-- Discard dependent rows before fitting a polynomial. The resulting
coordinate map is onto and uses no more rows than the original map. -/
theorem independent_predictor_coordinates {f : Q→V→A} {R : ℕ}
    (h : HasLinearCells f R) :
    ∃ r : ℕ,r≤R ∧ ∃ L : V→ₗ[F]Vec (Fin r),Surjective L ∧
      ∃ φ : Q→Vec (Fin r)→A,∀ q x,f q x=φ q (L x) := by
  classical
  obtain ⟨r,hr,L,φ,hφ⟩:=h
  let E:=(Module.finBasis F L.range).equivFun
  let L':=E.toLinearMap.comp L.rangeRestrict
  have hdim : Module.finrank F L.range≤r := by
    exact (Submodule.finrank_le L.range).trans_eq (by simp [Vec])
  have hsurj : Surjective L.rangeRestrict := by
    rintro ⟨v,hv⟩
    obtain ⟨x,rfl⟩:=hv
    exact ⟨x,rfl⟩
  refine ⟨Module.finrank F L.range,hdim.trans hr,L',
    E.surjective.comp hsurj,fun q x=>φ q (E.symm x).val,?_⟩
  intro q x
  simp only [L',LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  exact hφ q x

end
end Lax793645Proofs.Simplifications
