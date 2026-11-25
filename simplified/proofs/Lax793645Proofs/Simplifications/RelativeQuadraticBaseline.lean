import Lax793645Proofs.Simplifications.RelativeQuadraticExtension
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H C : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H] [AddCommGroup C] [Module QField C]

/-- A compatible partial lift through a surjective linear map extends
using at most the frozen dimension plus the target dimension. -/
theorem relative_linear_lift [FiniteDimensional QField B]
    [FiniteDimensional QField H] [FiniteDimensional QField C]
    (T : H→ₗ[QField] C) (hT : Function.Surjective T)
    (S : Submodule QField B) (g₀ : S→ₗ[QField] H) (ell : B→ₗ[QField] C)
    (hcompat : T.comp g₀=ell.comp S.subtype) :
    ∃ g : B→ₗ[QField] H,g.comp S.subtype=g₀ ∧ T.comp g=ell ∧
      Module.finrank QField g.range≤Module.finrank QField S+Module.finrank QField C := by
  obtain ⟨j,hj⟩ := T.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hT)
  obtain ⟨p,hp⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let a := j.comp ell
  let d := g₀-a.comp S.subtype
  let g := a+d.comp p
  have ha : T.comp a=ell := by
    dsimp only [a]
    rw [←LinearMap.comp_assoc,hj,LinearMap.id_comp]
  have hd : T.comp d=0 := by
    dsimp only [d]
    rw [LinearMap.comp_sub,hcompat,←LinearMap.comp_assoc,ha,sub_self]
  refine ⟨g,?_,?_,?_⟩
  · apply LinearMap.ext
    intro f
    change a (f:B)+d (p (f:B))=g₀ f
    have hx : p (f:B)=f := LinearMap.congr_fun hp f
    rw [hx]
    change a (f:B)+(g₀ f-a (f:B))=g₀ f
    abel
  · apply LinearMap.ext
    intro b
    change T (a b+d (p b))=ell b
    rw [map_add]
    have hb : T (a b)=ell b := LinearMap.congr_fun ha b
    have hz : T (d (p b))=0 := LinearMap.congr_fun hd (p b)
    rw [hb,hz,add_zero]
  · have hsum := rk_add_le a (d.comp p)
    have ha' : rk a≤Module.finrank QField C :=
      (rk_comp_le_left ell j).trans (LinearMap.finrank_range_le j)
    have hd' : rk (d.comp p)≤Module.finrank QField S :=
      (rk_comp_le_left p d).trans (LinearMap.finrank_range_le d)
    exact hsum.trans ((Nat.add_le_add ha' hd').trans_eq (Nat.add_comm _ _))

/-- The small linear baseline in the quadratic realization proposal.
No injectivity of the frozen channel map is needed. -/
theorem relative_quadratic_baseline [FiniteDimensional QField B] [FiniteDimensional QField H]
    (q : QuadraticForm QField H) (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule QField B) (C : Submodule QField H) (g₀ : S→ₗ[QField] H)
    (ell : B→ₗ[QField] C→ₗ[QField] QField)
    (hcompat : ∀ (f : S) (c : C),ell f c=q.polarBilin (g₀ f) c) :
    ∃ g : B→ₗ[QField] H,(∀ f : S,g f=g₀ f) ∧
      (∀ (b : B) (c : C),q.polarBilin (g b) c=ell b c) ∧
      Module.finrank QField g.range≤Module.finrank QField S+Module.finrank QField C := by
  let β : LinearMap.BilinForm QField H := q.polarBilin
  let T : H→ₗ[QField] C→ₗ[QField] QField := C.subtype.dualMap.comp β
  have hT : Function.Surjective T := by
    intro a
    obtain ⟨f,hf⟩ := LinearMap.dualMap_surjective_of_injective C.subtype_injective a
    refine ⟨(β.toDual hnd).symm f,?_⟩
    change C.subtype.dualMap (β ((β.toDual hnd).symm f))=a
    have he : β ((β.toDual hnd).symm f)=f := (β.toDual hnd).apply_symm_apply f
    rw [he,hf]
  have hc : T.comp g₀=ell.comp S.subtype := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro c
    exact (hcompat f c).symm
  obtain ⟨g,hg,hproj,hr⟩ := relative_linear_lift T hT S g₀ ell hc
  refine ⟨g,fun f=>LinearMap.congr_fun hg f,?_,?_⟩
  · intro b c
    exact LinearMap.congr_fun (LinearMap.congr_fun hproj b) c
  · simpa only [Subspace.dual_finrank_eq] using hr

end
end Lax793645Proofs.Simplifications
