import Lax793645Proofs.Simplifications.AsymmetricCommonProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

theorem banner_injective_output {D : Type} (ν f : Wgt A) (P : A→B)
    (E : B→D) (hE : Injective E) : banner ν (E∘P) f=banner ν P f := by
  funext x
  unfold banner cashbook mapW
  simp only [Function.comp_apply,hE.eq_iff]

theorem density_equivalence (E : A≃B) (ν p : Wgt A) :
    density (mapW ν E) (mapW p E)=(density ν p)∘E.symm := by
  funext x
  simp only [density,mapW_equiv_val,Function.comp_apply]

theorem cashbook_equivalence (E : A≃B) (ν f : Wgt A) (P : B→C) :
    cashbook (mapW ν E) P (f∘E.symm)=cashbook ν (P∘E) f := by
  have he : (fun x=>mapW ν E x*(f∘E.symm) x)=mapW (fun x=>ν x*f x) E := by
    ext x
    simp only [mapW_equiv_val,Function.comp_apply]
  funext c
  unfold cashbook
  rw [he,map_nested,map_nested]

theorem banner_equivalence_input (E : A≃B) (ν f : Wgt A) (P : B→C) :
    (banner (mapW ν E) P (f∘E.symm))∘E=banner ν (P∘E) f := by
  unfold banner
  rw [cashbook_equivalence]
  rfl

theorem dip_equivalence (E : A≃B) (ν f g : Wgt A) :
    dip (mapW ν E) (f∘E.symm) (g∘E.symm)=dip ν f g := by
  unfold dip
  rw [mapW_avg]
  simp only [Function.comp_apply,Equiv.symm_apply_apply]

theorem projected_overlap_equivalence (E : A≃B) (ν p q : Wgt A) (P : B→C) :
    dip (mapW ν E) (banner (mapW ν E) P (density (mapW ν E) (mapW p E)))
      (banner (mapW ν E) P (density (mapW ν E) (mapW q E)))=
    dip ν (banner ν (P∘E) (density ν p)) (banner ν (P∘E) (density ν q)) := by
  rw [density_equivalence,density_equivalence]
  unfold dip
  rw [mapW_avg]
  change avg ν (fun x=>((banner (mapW ν E) P ((density ν p)∘E.symm))∘E) x*
    ((banner (mapW ν E) P ((density ν q)∘E.symm))∘E) x)=_
  rw [banner_equivalence_input,banner_equivalence_input]

end
end Lax793645Proofs.Simplifications
