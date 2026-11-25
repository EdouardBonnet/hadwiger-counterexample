import Lax793645Proofs.Simplifications.GramFourCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

theorem constant_gram_resonance (A : Mat I I) (D : Wgt (KeyCoordinates I N))
    (c : F) (h : ∀ x,D x≠0 → gramPrimitive A x=c) (x y z : KeyCoordinates I N) :
    D x*D y*D z*D (x+y+z)*
      wsign (crossGram A A N x y+crossGram A A N x z+crossGram A A N y z)=
      D x*D y*D z*D (x+y+z) := by
  by_cases hx : D x=0
  · simp [hx]
  by_cases hy : D y=0
  · simp [hy]
  by_cases hz : D z=0
  · simp [hz]
  by_cases hw : D (x+y+z)=0
  · simp [hw]
  rw [gram_primitive_four_corner,h x hx,h y hy,h z hz,h _ hw]
  have hc : c+c+c+c=0 := by rw [char_two,zero_add,char_two]
  rw [hc,wsign_zero,mul_one]

/-- Four-corner cancellation needs a fixed primitive only in the resonant
case. This formulation permits quadratic Gram fibers as well as ordered
Gram fibers. -/
theorem fixed_gram_four_corner
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ x,|D x| ≤ 1) (hF : ∀ ξ,|linearFourier D ξ| ≤ δ)
    (A A' B B' C C' : Mat I I)
    (hres : A'=A → ∃ c:F,∀ x,D x≠0 → gramPrimitive A x=c)
    (ξ η ζ : KeyCoordinates I N) :
    |fourCorner (crossGram A A' N) (crossGram B B' N) (crossGram C C' N)
      (fun x=>vectorPhase ξ x*D x) (fun x=>vectorPhase η x*D x)
      (fun x=>vectorPhase ζ x*D x) D| ≤ δ^2+bp (-(N:ℝ)/2) := by
  let f (a : KeyCoordinates I N) (x : KeyCoordinates I N) := vectorPhase a x*D x
  have hf a x : |f a x| ≤ 1 := by
    simpa only [f,abs_mul,vectorPhase,wsign_abs,one_mul] using hD x
  have hhat a ν : |linearFourier (f a) ν| ≤ δ := by
    rw [show f a=(fun x=>vectorPhase a x*D x) from rfl,linear_fourier_modulate]
    exact hF _
  rcases gram_rank_alternative (N:=N) A A' B B' C C' with he|hr
  · rcases he with ⟨h1,h2,h3,h4,h5⟩
    obtain ⟨c,hc⟩:=hres h1
    subst A'
    subst B
    subst B'
    subst C
    subst C'
    have hev : fourCorner (crossGram A A N) (crossGram A A N) (crossGram A A N)
        (f ξ) (f η) (f ζ) D=
        avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
          f ξ x*f η y*f ζ z*D (x+y+z)))) := by
      apply avg_congr
      intro x _
      apply avg_congr
      intro y _
      apply avg_congr
      intro z _
      calc
        _=(vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z)*
          (D x*D y*D z*D (x+y+z)*
            wsign (crossGram A A N x y+crossGram A A N x z+crossGram A A N y z)) := by
              dsimp only [f]; ring
        _=_ := by rw [constant_gram_resonance A D c hc]; dsimp only [f]; ring
    change |fourCorner _ _ _ (f ξ) (f η) (f ζ) D| ≤ _
    rw [hev]
    exact (small_fourier_four_corner (f ξ) (f η) (f ζ) D δ hδ
      (hhat ξ) (hhat η) (hf ζ) hD).trans (le_add_of_nonneg_right (bp_pos _).le)
  · have hh := four_corner_max_rank (crossGram A A' N) (crossGram B B' N)
      (crossGram C C' N) (f ξ) (f η) (f ζ) D (hf ξ) (hf η) (hf ζ) hD
    refine hh.trans ((bp_le ?_).trans (le_add_of_nonneg_left (sq_nonneg δ)))
    exact div_le_div_of_nonneg_right (neg_le_neg (by exact_mod_cast hr)) (by norm_num)

theorem fixed_gram_modulation (M : Mat I I) (D : Wgt (KeyCoordinates I N))
    (c : F) (h : ∀ x,D x≠0 → gramPrimitive M x=c) (x : KeyCoordinates I N) :
    D x*wsign (gramPrimitive M x)=D x*wsign c := by
  by_cases hx : D x=0
  · simp only [hx,zero_mul]
  · rw [h x hx]

theorem full_fixed_gram_four_corner
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ x,|D x| ≤ 1) (hF : ∀ ξ,|linearFourier D ξ| ≤ δ)
    (A A' B B' C C' M0 M1 M2 : Mat I I)
    (hres : A'=A → ∃ c:F,∀ x,D x≠0 → gramPrimitive A x=c)
    (c0 c1 c2 : F)
    (h0 : ∀ x,D x≠0 → gramPrimitive M0 x=c0)
    (h1 : ∀ x,D x≠0 → gramPrimitive M1 x=c1)
    (h2 : ∀ x,D x≠0 → gramPrimitive M2 x=c2)
    (ξ η ζ : KeyCoordinates I N) :
    |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      D x*D y*D z*D (x+y+z)*vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z+
          gramPrimitive M0 x+gramPrimitive M1 y+gramPrimitive M2 z))))| ≤ 
      δ^2+bp (-(N:ℝ)/2) := by
  let c:=wsign c0*wsign c1*wsign c2
  have he x y z :
      D x*D y*D z*D (x+y+z)*vectorPhase ξ x*vectorPhase η y*vectorPhase ζ z*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z+
          gramPrimitive M0 x+gramPrimitive M1 y+gramPrimitive M2 z)=
      c*((vectorPhase ξ x*D x)*(vectorPhase η y*D y)*(vectorPhase ζ z*D z)*D (x+y+z)*
        wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z)) := by
    rw [wsign_add,wsign_add,wsign_add]
    calc
      _=(D x*wsign (gramPrimitive M0 x))*(D y*wsign (gramPrimitive M1 y))*
        (D z*wsign (gramPrimitive M2 z))*(D (x+y+z)*vectorPhase ξ x*vectorPhase η y*
          vectorPhase ζ z*wsign (crossGram A A' N x y+crossGram B B' N x z+crossGram C C' N y z)) := by ring
      _=_ := by
        rw [fixed_gram_modulation M0 D c0 h0,fixed_gram_modulation M1 D c1 h1,
          fixed_gram_modulation M2 D c2 h2]
        dsimp only [c]; ring
  simp_rw [he,avg_mul']
  rw [abs_mul]
  have hc : |c|=1:=by simp only [c,abs_mul,wsign_abs,one_mul]
  rw [hc,one_mul]
  exact fixed_gram_four_corner D δ hδ hD hF A A' B B' C C' hres ξ η ζ

end
end Lax793645Proofs.Simplifications
