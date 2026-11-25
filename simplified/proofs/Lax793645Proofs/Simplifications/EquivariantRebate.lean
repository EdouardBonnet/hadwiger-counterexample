import Lax793645Proofs.Simplifications.SuccessfulFiniteProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem mcut_equivalence (E : A≃B) (ν p : Wgt A) (R : ℝ) :
    mcut R (mapW ν E) (mapW p E)=(mcut R ν p)∘E.symm := by
  unfold mcut
  rw [density_equivalence]
  rfl

theorem rebate_equivalence (E : A≃B) (ν f g : Wgt A) (P : B→C) :
    rebate (mapW ν E) (f∘E.symm) (g∘E.symm) P=rebate ν f g (P∘E) := by
  unfold rebate
  rw [dip_equivalence]
  congr 1
  unfold dip
  rw [mapW_avg]
  change avg ν (fun x=>((banner (mapW ν E) P (f∘E.symm))∘E) x*
    ((banner (mapW ν E) P (g∘E.symm))∘E) x)=_
  rw [banner_equivalence_input,banner_equivalence_input]

theorem rebate_injective_output {D : Type} (ν f g : Wgt A) (P : A→B)
    (E : B→D) (hE : Injective E) : rebate ν f g (E∘P)=rebate ν f g P := by
  unfold rebate
  rw [banner_injective_output ν f P E hE,banner_injective_output ν g P E hE]

end
end Lax793645Proofs.Simplifications
