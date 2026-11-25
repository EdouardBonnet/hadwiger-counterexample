import Lax793645Proofs.Simplifications.FourierNorm

/-! # Linear weights on four-corner queries

The small-Fourier estimate survives arbitrary linear pullbacks of weights
with bounded Fourier norm. It also tensorizes over independent query blocks.
The cap, Gram constraints, and dependent nominal inputs still need the
separate high-moment assembly.
-/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Fourier-bounded weights can be tested through their individual pulled
back characters, including when the pullback is not injective. -/
theorem fourier_pullback_bound {A : Type} [Fintype A]
    (μ : Wgt A) (F : Wgt A) (K : A→Vec J) (w : Wgt (Vec J)) (ε : ℝ)
    (h : ∀ ξ,|avg μ (fun x=>F x*vectorPhase ξ (K x))|≤ε) :
    |avg μ (fun x=>F x*w (K x))|≤ε*fourierNorm w := by
  have he (x : A) : F x*w (K x)=
      ∑ ξ:Vec J,linearFourier w ξ*(F x*vectorPhase ξ (K x)) := by
    rw [←hat_eqn w (K x),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    unfold linearFourier
    ring
  simp_rw [he,avg_sum,avg_mul']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [abs_mul]
  refine (Finset.sum_le_sum (fun ξ _=>mul_le_mul_of_nonneg_left (h ξ) (abs_nonneg _))).trans_eq ?_
  rw [←Finset.sum_mul,mul_comm]
  rfl

omit [DecidableEq I] [DecidableEq J] in
private theorem phase_pullback (M : Mat J I) (ξ : Vec J) (x : Vec I) :
    vectorPhase ξ (M*ᵥx)=vectorPhase (Mᵀ*ᵥξ) x := by
  unfold vectorPhase
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

/-- Pulling a function back by a linear map cannot increase its Fourier
norm; noninjectivity only combines Fourier coefficients. -/
theorem fourier_norm_linear_pullback (M : Mat J I) (w : Wgt (Vec J)) :
    fourierNorm (fun x=>w (M*ᵥx))≤fourierNorm w := by
  have he (x : Vec I) : w (M*ᵥx)=
      ∑ ξ:Vec J,linearFourier w ξ*vectorPhase (Mᵀ*ᵥξ) x := by
    rw [←hat_eqn w (M*ᵥx)]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [phase_pullback]
    rfl
  simp_rw [he]
  exact (fourier_norm_sum _).trans_eq (by
    simp_rw [fourier_norm_smul,fourier_norm_character,mul_one]
    rfl)

/-- A bounded function on m binary coordinates has Fourier norm at most
2^(m/2). This charges low-rank phase corrections through their small image. -/
theorem fourier_norm_bounded (w : Wgt (Vec I)) (hw : ∀ x,|w x|≤1) :
    fourierNorm w≤bp (num I/2) := by
  have hs : ∑ ξ:Vec I,(linearFourier w ξ)^2≤1 := by
    rw [linear_fourier_parseval]
    apply unif_law.avg_le
    intro x
    have hx := abs_le.mp (hw x)
    nlinarith [hx.1,hx.2]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun _ : Vec I=>(1:ℝ)) (fun ξ=>|linearFourier w ξ|)
  simp only [one_mul,one_pow,sq_abs,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one] at hcs
  rw [card_space,dim_vec] at hcs
  have hh : (fourierNorm w)^2≤bp (num I) := hcs.trans
    ((mul_le_mul_of_nonneg_left hs (bp_pos _).le).trans_eq (mul_one _))
  exact (le_abs_self _).trans (half_power _ _ hh)

private theorem vector_product_average {T : Type} [Fintype T] [DecidableEq T]
    (f : T→Wgt (Vec I)) :
    avg unif (fun x : Vec (T×I)=>∏ t,f t (fun i=>x (t,i)))=
      ∏ t,avg unif (f t) := by
  classical
  let E : Vec (T×I)≃(T→Vec I) :=
    ⟨fun x t i=>x (t,i),fun x v=>x v.1 v.2,fun _=>rfl,fun _=>rfl⟩
  change avg unif (fun x=>prodW f (E x))=_
  rw [←mapW_avg,unif_equiv,draws_unif]
  exact prodW_avg _ _

/-- Tensorization of the ordinary linear Fourier transform over query blocks. -/
theorem linear_fourier_product {T : Type} [Fintype T] [DecidableEq T]
    (f : T→Wgt (Vec I)) (ξ : Vec (T×I)) :
    linearFourier (fun x=>∏ t,f t (fun i=>x (t,i))) ξ=
      ∏ t,linearFourier (f t) (fun i=>ξ (t,i)) := by
  have he (x : Vec (T×I)) : vectorPhase ξ x=
      ∏ t,vectorPhase (fun i=>ξ (t,i)) (fun i=>x (t,i)) := by
    unfold vectorPhase dotProduct
    rw [Fintype.sum_prod_type,wsign_sum]
  unfold linearFourier
  simp_rw [he,←Finset.prod_mul_distrib]
  exact vector_product_average (fun t x=>vectorPhase (fun i=>ξ (t,i)) x*f t x)

/-- Independent query blocks retain the product of their small Fourier
coefficients even after a joint weight of bounded Fourier norm is inserted. -/
theorem fourier_product_weight {T : Type} [Fintype T] [DecidableEq T]
    (f : T→Wgt (Vec I)) (ε : T→ℝ)
    (hf : ∀ t ξ,|linearFourier (f t) ξ|≤ε t)
    (w : Wgt (Vec (T×I))) :
    |avg unif (fun x=>(∏ t,f t (fun i=>x (t,i)))*w x)|≤
      (∏ t,ε t)*fourierNorm w := by
  apply fourier_pullback_bound unif _ id w (∏ t,ε t)
  intro ξ
  have he : avg unif (fun x=>(∏ t,f t (fun i=>x (t,i)))*vectorPhase ξ x)=
      linearFourier (fun x=>∏ t,f t (fun i=>x (t,i))) ξ := by
    unfold linearFourier
    apply avg_congr
    intro x _
    ring
  simp only [id_eq]
  rw [he,linear_fourier_product,Finset.abs_prod]
  exact Finset.prod_le_prod (fun t _=>abs_nonneg _) (fun t _=>hf t _)

/-- Arbitrary linear weights retain the small four-corner bound at the cost
of their Fourier norm. In particular this covers the injectivity polynomial
and the linear expansions of low-rank Gram corrections. -/
theorem small_fourier_weighted_four_corner
    (f0 f1 f2 f3 : Wgt (Vec I)) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ ξ,|linearFourier f0 ξ|≤δ) (h1 : ∀ ξ,|linearFourier f1 ξ|≤δ)
    (h2 : ∀ x,|f2 x|≤1) (h3 : ∀ x,|f3 x|≤1)
    (M0 M1 M2 : Mat J I) (w : Wgt (Vec J)) :
    |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      f0 x*f1 y*f2 z*f3 (x+y+z)*w (M0*ᵥx+M1*ᵥy+M2*ᵥz))))|≤
      δ^2*fourierNorm w := by
  have hc (ξ : Vec J) :
      |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
        f0 x*f1 y*f2 z*f3 (x+y+z)*vectorPhase ξ (M0*ᵥx+M1*ᵥy+M2*ᵥz))))|≤δ^2 := by
    let g0 (x : Vec I) := vectorPhase (M0ᵀ*ᵥξ) x*f0 x
    let g1 (x : Vec I) := vectorPhase (M1ᵀ*ᵥξ) x*f1 x
    let g2 (x : Vec I) := vectorPhase (M2ᵀ*ᵥξ) x*f2 x
    have hg0 (ζ : Vec I) : |linearFourier g0 ζ|≤δ := by
      rw [show g0=(fun x=>vectorPhase (M0ᵀ*ᵥξ) x*f0 x) from rfl,linear_fourier_modulate]
      exact h0 _
    have hg1 (ζ : Vec I) : |linearFourier g1 ζ|≤δ := by
      rw [show g1=(fun x=>vectorPhase (M1ᵀ*ᵥξ) x*f1 x) from rfl,linear_fourier_modulate]
      exact h1 _
    have hg2 (x : Vec I) : |g2 x|≤1 := by
      dsimp [g2]
      rw [abs_mul,vectorPhase,wsign_abs,one_mul]
      exact h2 x
    have hchar (x y z : Vec I) :
        vectorPhase ξ (M0*ᵥx+M1*ᵥy+M2*ᵥz)=
          vectorPhase (M0ᵀ*ᵥξ) x*vectorPhase (M1ᵀ*ᵥξ) y*vectorPhase (M2ᵀ*ᵥξ) z := by
      rw [←phase_pullback,←phase_pullback,←phase_pullback]
      simp only [vectorPhase,dotProduct_add,wsign_add]
    have he (x y z : Vec I) :
        f0 x*f1 y*f2 z*f3 (x+y+z)*vectorPhase ξ (M0*ᵥx+M1*ᵥy+M2*ᵥz)=
          g0 x*g1 y*g2 z*f3 (x+y+z) := by
      rw [hchar]
      dsimp [g0,g1,g2]
      ring
    simp_rw [he]
    exact small_fourier_four_corner g0 g1 g2 f3 δ hδ hg0 hg1 hg2 h3
  let μ : Wgt (Vec I×Vec I×Vec I) := pairW unif (pairW unif unif)
  let F (v : Vec I×Vec I×Vec I) := f0 v.1*f1 v.2.1*f2 v.2.2*f3 (v.1+v.2.1+v.2.2)
  let K (v : Vec I×Vec I×Vec I) := M0*ᵥv.1+M1*ᵥv.2.1+M2*ᵥv.2.2
  simpa only [μ,F,K,pairW_avg] using
    fourier_pullback_bound μ F K w (δ^2) (fun ξ=>by simpa only [μ,F,K,pairW_avg] using hc ξ)

end
end Lax793645Proofs.Simplifications
