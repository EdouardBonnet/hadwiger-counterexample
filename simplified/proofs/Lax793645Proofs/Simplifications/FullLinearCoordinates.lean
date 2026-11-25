import Lax793645Proofs.Simplifications.FullLinearCells

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q A : Type} [AddCommGroup V] [Module F V]

/-- Remove redundant rows from a full linear partition. The remaining
coordinates are onto, and the color map is injective for each displayed
diagonal bit. -/
theorem full_linear_coordinates {f : Q→V→A} {R : ℕ}
    (h : HasFullLinearCells f R) :
    ∃ r : ℕ,r≤R ∧ ∃ L : V→ₗ[F]Vec (Fin r),Surjective L ∧
      ∃ ι : Q→Vec (Fin r)→A,(∀ q,Injective (ι q)) ∧
        ∀ q x,f q x=ι q (L x) := by
  classical
  obtain ⟨r,hr,L,hL⟩:=h
  let E:(range L)≃ₗ[F]Vec (Fin (dim (range L))):=(Module.finBasis F (range L)).equivFun
  let P:=E.toLinearMap.comp L.rangeRestrict
  have hP : Surjective P:=E.surjective.comp L.surjective_rangeRestrict
  obtain ⟨j,hj⟩:=P.exists_rightInverse_of_surjective (range_eq_top.mpr hP)
  have hj' (z : Vec (Fin (dim (range L)))) : P (j z)=z := by
    exact LinearMap.congr_fun hj z
  have he (q : Q) (x y : V) : f q x=f q y ↔ P x=P y := by
    rw [hL q]
    constructor
    · intro hh
      exact congrArg E (Subtype.ext hh)
    · intro hh
      exact congrArg Subtype.val (E.injective hh)
  refine ⟨dim (range L),?_,P,hP,fun q z=>f q (j z),?_,?_⟩
  · exact (Submodule.finrank_le _).trans (by simpa only [dim_vec,Fintype.card_fin] using hr)
  · intro q x y hxy
    simpa only [hj'] using (he q (j x) (j y)).mp hxy
  · intro q x
    exact (he q x (j (P x))).mpr (hj' (P x)).symm

end
end Lax793645Proofs.Simplifications
