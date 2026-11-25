import Lax793645Proofs.Simplifications.FreeChannelMarginals
import Lax793645Proofs.Simplifications.QuadraticChannelFrames
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.AmbientBatchSlots

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniform conditioning is preserved by an exact change of coordinates. -/
theorem uniform_condition_equiv {A D : Type} [Fintype A] [Fintype D] [Nonempty A]
    (E : A≃D) (P : A→Prop) : mapW (unifOn P) E=unifOn (fun x=>P (E.symm x)) := by
  classical
  have : Nonempty D:=⟨E (Classical.choice (inferInstance : Nonempty A))⟩
  have hmap {w : Wgt A} (Q : D→Prop) :
      mapW (onW w (Q∘E)) E=onW (mapW w E) Q := by
    funext y
    rw [mapW,pr_on,onW_val,mapW_pr]
    congr 1
    change pr w (fun x=>Q (E x) ∧ E x=y)=pr w (fun x=>E x=y)*ind (Q y)
    simp only [pr,avg,ind_and,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : E x=y
    · simp only [h,ind_true,mul_one]
    · simp only [ind_zero h,mul_zero,zero_mul]
  have he : P=(fun x=>P (E.symm x))∘E := by funext x;simp
  rw [←on_unif,he,hmap,unif_equiv,on_unif]
  congr 1
  funext x
  simp

variable {B C V : Type} [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
  [AddCommGroup V] [Module F V]

def quadraticChannelSplit : (QuadraticFull B C→ₗ[F]V)≃ₗ[F]
    ((B×C→ₗ[F]V)×(C→ₗ[F]V)) :=
  (LinearEquiv.arrowCongr (LinearEquiv.prodAssoc F B C C).symm
    (LinearEquiv.refl F V)).trans (LinearMap.coprodEquiv F).symm

theorem quadratic_channel_split_first (f : QuadraticFull B C→ₗ[F]V) (b : B) (c : C) :
    (quadraticChannelSplit f).1 (b,c)=f (b,(c,0)) := rfl

theorem quadratic_channel_split_second (f : QuadraticFull B C→ₗ[F]V) (c : C) :
    (quadraticChannelSplit f).2 c=f (0,(0,c)) := rfl

theorem quadratic_channel_split_injective (f : QuadraticFull B C→ₗ[F]V) :
    Function.Injective f↔Function.Injective
      ((quadraticChannelSplit f).1.coprod (quadraticChannelSplit f).2) := by
  have he : (quadraticChannelSplit f).1.coprod (quadraticChannelSplit f).2=
      f.comp (LinearEquiv.prodAssoc F B C C).toLinearMap := by
    apply LinearMap.ext
    rintro ⟨⟨b,c⟩,d⟩
    change f (b,(c,0))+f (0,(0,d))=f (b,(c,d))
    rw [←map_add]
    simp
  rw [he]
  constructor
  · intro h;exact h.comp (LinearEquiv.prodAssoc F B C C).injective
  intro h x y heq
  have hh:=h (a₁:=(LinearEquiv.prodAssoc F B C C).symm x)
    (a₂:=(LinearEquiv.prodAssoc F B C C).symm y) (by simpa using heq)
  exact (LinearEquiv.prodAssoc F B C C).symm.injective hh

def quadraticPXValid (q : QuadraticForm F V) (Q : QuadraticForm F B)
    (g : B×C→ₗ[F]V) : Prop :=
  Function.Injective g ∧ (∀ b,q (g (b,0))=Q b) ∧
    ∀ c b,q.polarBilin (g (0,c)) (g (b,0))=0

theorem quadratic_channel_split_valid (q : QuadraticForm F V) (Q : QuadraticForm F B)
    (f : QuadraticFull B C→ₗ[F]V) : quadraticChannelValid q Q f↔
      quadraticPXValid q Q (quadraticChannelSplit f).1 ∧
      Function.Injective ((quadraticChannelSplit f).1.coprod (quadraticChannelSplit f).2) := by
  constructor
  · intro hf
    obtain ⟨hi,hq,hx⟩:=quadratic_channel_frame_data q Q f hf
    refine ⟨⟨?_,hq,hx⟩,(quadratic_channel_split_injective f).mp hi⟩
    intro u v he
    have hh:=hi he
    change (u.1,(u.2,0))=(v.1,(v.2,0)) at hh
    apply Prod.ext
    · exact congrArg (fun z : QuadraticFull B C=>z.1) hh
    · exact congrArg (fun z : QuadraticFull B C=>z.2.1) hh
  · rintro ⟨⟨_,hq,hx⟩,hi⟩
    refine ⟨(quadratic_channel_split_injective f).mpr hi,?_,?_⟩
    · apply QuadraticMap.ext
      exact hq
    intro c b
    change (q.comp f).polarBilin (quadraticXIn c) (quadraticPrimalIn b)=0
    have hx' : q.polarBilin (f (quadraticXIn c)) (f (quadraticPrimalIn b))=0 := hx c b
    simpa only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      QuadraticMap.comp_apply,map_add] using hx'

end
end Lax793645Proofs.Simplifications
