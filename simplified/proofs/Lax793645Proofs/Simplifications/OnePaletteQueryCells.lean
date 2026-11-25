import Lax793645Proofs.Simplifications.OnePaletteCoordinates
import Lax793645Proofs.Simplifications.OnePolynomialInputs
import Lax793645Proofs.Simplifications.ExactSupportFamilies

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}

theorem one_face_primal (x : Appearance p) (o : OneOrient p n N) (z : Knobs p.g n) :
    oneFace x o z=oneStarKey x.l (onePrimalKey o (spring p x.l x.s x.f z)) := by
  funext e
  rfl

def onePaletteInput (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r)) :
    Knobs p.g n→ₗ[F]Vec (Fin r):=
  L.comp ((oneStarKey x.l).comp ((onePrimalKey o).comp (springLinear p x.l x.s x.f)))

def onePaletteFree (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r)) :
    Vec (Fin n)→ₗ[F]Vec (Fin r):=
  L.comp ((oneStarKey x.l).comp (oneFreeKey (oneFreeColumns p n x.s) o))

theorem one_palette_input_affine (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r)) (z : Knobs p.g n) :
    L (oneFace x o z)=onePaletteInput x o L z+L (oneFace x o 0) := by
  simp only [one_face_primal,onePaletteInput,LinearMap.comp_apply,springLinear,
    LinearMap.coe_mk,AddHom.coe_mk,map_sub,sub_add_cancel]

theorem one_palette_input_add_free (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r))
    (z : Knobs p.g n) (v : Vec (Fin n)) :
    L (oneFace x o (z+freeKnob p n v))=
      L (oneFace x o z)+onePaletteFree x o L v := by
  simp only [one_face_primal]
  rw [spring_add_free,map_add,map_add,map_add,one_primal_key_free]
  rfl

theorem one_palette_linear_free (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r)) (v : Vec (Fin n)) :
    onePaletteInput x o L (freeKnob p n v)=onePaletteFree x o L v := by
  have hh:=one_palette_input_add_free x o L 0 v
  rw [zero_add,one_palette_input_affine] at hh
  exact add_right_cancel (hh.trans (add_comm _ _))

/-- Every full coordinate cell contains an input with each permitted
diagonal value. The free block moves the cell while leaving the tester
bit unchanged. -/
theorem one_palette_input_cells (x : Appearance p) (o : OneOrient p n N)
    (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin r))
    (hfree : Surjective (onePaletteFree x o L))
    (hx : x.apt) (hp : 1≤p.r) (hn : 2*p.r≤n) :
    ∃ S : Vec (Fin r)→ₗ[F]Knobs p.g n,
      (∀ c,onePaletteInput x o L (S c)=c) ∧
      ∀ c,∃ z,dialed p x.l x.f z=x.q ∧
        onePaletteInput x o L z+L (oneFace x o 0)=c := by
  classical
  obtain ⟨j,hj⟩:=(onePaletteFree x o L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hfree)
  have hj' c:onePaletteFree x o L (j c)=c:=LinearMap.congr_fun hj c
  refine ⟨(freeKnob p n).comp j,fun c=>?_,?_⟩
  · rw [LinearMap.comp_apply,one_palette_linear_free,hj']
  obtain ⟨z,hz⟩:=law_support_nonempty (x.wit n) (Appearance.witLaw hx hp hn)
  have hq : dialed p x.l x.f z=x.q := by
    by_contra h
    have he : x.wit n z=0 := by
      simp only [Appearance.wit,scopedBit,onW_val,ind_zero h,mul_zero,zero_div]
    exact hz.ne' he
  intro c
  let v:=j (c-L (oneFace x o z))
  refine ⟨z+freeKnob p n v,?_,?_⟩
  · rw [dialed_add_free,hq]
  · rw [←one_palette_input_affine,one_palette_input_add_free]
    change L (oneFace x o z)+onePaletteFree x o L (j (c-L (oneFace x o z)))=c
    rw [hj',add_sub_cancel]

end
end Lax793645Proofs.Simplifications
