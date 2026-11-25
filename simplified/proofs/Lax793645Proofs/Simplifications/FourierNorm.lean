import Lax793645Proofs.Simplifications.LinearFourier

/-! # Fourier-norm control of query weights

Linear constraints have Fourier norm at most one. Multiplication is
submultiplicative, so finite combinations of such constraints can be tracked
without paying the ambient dimension. The final lemmas reduce arbitrary
orientation-dependent Fourier-bounded weights to a single nonnegative moment.
They do not assert the required bound on that moment.
-/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def fourierNorm (f : Wgt (Vec I)) : ℝ := ∑ ξ:Vec I,|linearFourier f ξ|

theorem fourier_norm_nonneg (f : Wgt (Vec I)) : 0≤fourierNorm f :=
  Finset.sum_nonneg (fun _ _=>abs_nonneg _)

theorem linear_fourier_modulate (f : Wgt (Vec I)) (ζ ξ : Vec I) :
    linearFourier (fun x=>vectorPhase ζ x*f x) ξ=linearFourier f (ξ+ζ) := by
  unfold linearFourier
  apply avg_congr
  intro x _
  simp only [vectorPhase,add_dotProduct,wsign_add]
  ring

theorem linear_fourier_character (ζ ξ : Vec I) :
    linearFourier (vectorPhase ζ) ξ=ind (ξ=ζ) := by
  unfold linearFourier
  rw [vector_expand]
  apply avg_congr
  intro x _
  simp only [vectorPhase]
  rw [dotProduct_comm ξ x,dotProduct_comm ζ x]

theorem fourier_norm_character (ζ : Vec I) : fourierNorm (vectorPhase ζ)=1 := by
  classical
  simp only [fourierNorm,linear_fourier_character,abs_of_nonneg (ind_nonneg _)]
  rw [Finset.sum_eq_single ζ]
  · simp [ind]
  · intro ξ _ hξ
    simp [ind,hξ]
  · simp

theorem linear_fourier_mul (f g : Wgt (Vec I)) (ξ : Vec I) :
    linearFourier (fun x=>f x*g x) ξ=
      ∑ ζ:Vec I,linearFourier g ζ*linearFourier f (ξ+ζ) := by
  have he (x : Vec I) : g x=∑ ζ:Vec I,linearFourier g ζ*vectorPhase ζ x :=
    (hat_eqn g x).symm
  have hprod (x : Vec I) : f x*g x=
      ∑ ζ:Vec I,linearFourier g ζ*(vectorPhase ζ x*f x) := by
    rw [he x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ζ _
    ring
  change avg unif (fun x=>vectorPhase ξ x*(f x*g x))=_
  simp_rw [hprod,Finset.mul_sum,avg_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  unfold linearFourier
  conv_rhs => rw [←avg_mul']
  apply avg_congr
  intro x _
  simp only [vectorPhase,add_dotProduct,wsign_add]
  ring

theorem fourier_norm_mul (f g : Wgt (Vec I)) :
    fourierNorm (fun x=>f x*g x)≤fourierNorm f*fourierNorm g := by
  classical
  unfold fourierNorm
  simp_rw [linear_fourier_mul]
  refine (Finset.sum_le_sum (fun ξ _=>Finset.abs_sum_le_sum_abs _ _)).trans_eq ?_
  simp_rw [abs_mul]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  have he (ζ : Vec I) : (∑ ξ:Vec I,|linearFourier f (ξ+ζ)|)=
      ∑ ξ:Vec I,|linearFourier f ξ| :=
    Equiv.sum_comp (Equiv.addRight ζ) (fun ξ=>|linearFourier f ξ|)
  simp_rw [he]
  rw [←Finset.sum_mul,mul_comm]

theorem fourier_norm_add (f g : Wgt (Vec I)) :
    fourierNorm (fun x=>f x+g x)≤fourierNorm f+fourierNorm g := by
  unfold fourierNorm linearFourier
  simp_rw [mul_add,avg_add]
  exact (Finset.sum_le_sum (fun ξ _=>abs_add_le _ _)).trans_eq (Finset.sum_add_distrib ..)

theorem fourier_norm_smul (c : ℝ) (f : Wgt (Vec I)) :
    fourierNorm (fun x=>c*f x)=|c| * fourierNorm f := by
  unfold fourierNorm linearFourier
  simp_rw [mul_left_comm _ c,avg_mul',abs_mul]
  rw [Finset.mul_sum]

theorem fourier_norm_const (c : ℝ) : fourierNorm (fun _ : Vec I=>c)=|c| := by
  have he : (fun _ : Vec I=>c)=(fun x=>c*vectorPhase 0 x) := by
    ext x
    simp only [vectorPhase,zero_dotProduct,wsign_zero,mul_one]
  rw [he,fourier_norm_smul,fourier_norm_character,mul_one]

theorem fourier_norm_sum {T : Type} [Fintype T] (f : T→Wgt (Vec I)) :
    fourierNorm (fun x=>∑ t,f t x)≤∑ t,fourierNorm (f t) := by
  unfold fourierNorm linearFourier
  simp_rw [Finset.mul_sum,avg_sum]
  exact (Finset.sum_le_sum (fun ξ _=>Finset.abs_sum_le_sum_abs _ _)).trans_eq
    (Finset.sum_comm ..)

theorem fourier_norm_avg {T : Type} [Fintype T] (w : Wgt T)
    (hw : ∀ t,0≤w t) (f : T→Wgt (Vec I)) :
    fourierNorm (fun x=>avg w (fun t=>f t x))≤avg w (fun t=>fourierNorm (f t)) := by
  unfold avg
  refine (fourier_norm_sum (fun t x=>w t*f t x)).trans_eq ?_
  simp_rw [fourier_norm_smul,abs_of_nonneg (hw _)]

/-- Linear kernel indicators have Fourier norm at most one, regardless of
their codimension. They therefore add no Fourier-norm loss to a term. -/
theorem fourier_norm_kernel {J : Type} [Fintype J] [DecidableEq J]
    (A : Mat J I) : fourierNorm (fun x=>ind (A*ᵥx=0))≤1 := by
  have he (x : Vec I) : ind (A*ᵥx=0)=
      avg unif (fun y : Vec J=>vectorPhase (Aᵀ*ᵥy) x) := by
    rw [vector_expand]
    apply avg_congr
    intro y _
    simp only [vectorPhase,dotProduct_zero,wsign_zero,mul_one]
    congr 1
    rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]
  simp_rw [he]
  exact (fourier_norm_avg unif unif_law.nz _).trans_eq
    (by simp_rw [fourier_norm_character]; exact unif_law.avg_const 1)

/-- Uniform control of every Fourier-bounded input weight by one nonnegative
fourth moment. The weight may be chosen after the orientation is known. -/
theorem fourier_weight_fourth (f w : Wgt (Vec I)) (b : ℝ) (hb : 0≤b)
    (hw : fourierNorm w≤b) :
    |avg unif (fun x=>f x*w x)|^4≤
      b^4*avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
        f x*f y*f z*f (x+y+z)))) := by
  classical
  obtain ⟨ξ,_,hξ⟩ := Finset.exists_max_image univ
    (fun ξ:Vec I=>|linearFourier f ξ|) Finset.univ_nonempty
  have hc : |avg unif (fun x=>f x*w x)|≤b*|linearFourier f ξ| := by
    rw [linear_fourier_pair]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul]
    calc
      _≤∑ ζ:Vec I,|linearFourier f ξ| * |linearFourier w ζ| :=
        Finset.sum_le_sum (fun ζ _=>mul_le_mul_of_nonneg_right
          (hξ ζ (Finset.mem_univ _)) (abs_nonneg _))
      _=fourierNorm w*|linearFourier f ξ| := by rw [←Finset.mul_sum,mul_comm]; rfl
      _≤_ := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have hs : |linearFourier f ξ|^4≤∑ ζ:Vec I,(linearFourier f ζ)^4 := by
    rw [show |linearFourier f ξ|^4=(linearFourier f ξ)^4 by
      rw [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs,←pow_mul]]
    exact Finset.single_le_sum (f:=fun ζ:Vec I=>(linearFourier f ζ)^4)
      (fun ζ _=>by positivity)
      (Finset.mem_univ ξ)
  rw [linear_fourier_four_corner]
  have he : (∑ ζ:Vec I,linearFourier f ζ*linearFourier f ζ*
      linearFourier f ζ*linearFourier f ζ)=∑ ζ:Vec I,(linearFourier f ζ)^4 := by
    apply Finset.sum_congr rfl
    intro ζ _
    ring
  rw [he]
  refine (pow_le_pow_left₀ (abs_nonneg _) hc 4).trans ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hs (pow_nonneg hb _)

theorem fourier_weight_moment (f w : Wgt (Vec I)) (b : ℝ) (hb : 0≤b)
    (hw : fourierNorm w≤b) (ℓ : ℕ) :
    |avg unif (fun x=>f x*w x)|^(4*ℓ)≤
      b^(4*ℓ)*(avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
        f x*f y*f z*f (x+y+z)))))^ℓ := by
  have hh := pow_le_pow_left₀ (pow_nonneg (abs_nonneg _) 4)
    (fourier_weight_fourth f w b hb hw) ℓ
  simpa only [mul_pow,←pow_mul] using hh

theorem four_corner_nonneg (f : Wgt (Vec I)) :
    0≤avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      f x*f y*f z*f (x+y+z)))) := by
  rw [linear_fourier_four_corner]
  apply Finset.sum_nonneg
  intro ξ _
  nlinarith [sq_nonneg ((linearFourier f ξ)^2)]

/-- A capped leaf is charged only after the nonnegative high moment has
been formed. Input weights can depend on the full orientation. -/
theorem capped_fourier_weight_moment {O : Type} [Fintype O]
    (μ π : Wgt O) (f w : O→Wgt (Vec I)) (b C : ℝ)
    (hπ : ∀ o,0≤π o) (hcap : ∀ o,π o≤C*μ o)
    (hb : 0≤b) (hw : ∀ o,fourierNorm (w o)≤b) (ℓ : ℕ) :
    avg π (fun o=>|avg unif (fun x=>f o x*w o x)|^(4*ℓ))≤
      C*b^(4*ℓ)*avg μ (fun o=>(avg unif (fun x=>avg unif (fun y=>avg unif
        (fun z=>f o x*f o y*f o z*f o (x+y+z)))))^ℓ) := by
  refine (avg_mono hπ (fun o=>fourier_weight_moment (f o) (w o) b hb (hw o) ℓ)).trans ?_
  unfold avg
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hnon := mul_nonneg (pow_nonneg hb (4*ℓ))
    (pow_nonneg (four_corner_nonneg (f o)) ℓ)
  exact (mul_le_mul_of_nonneg_right (hcap o) hnon).trans_eq (by simp only [avg]; ring)

end
end Lax793645Proofs.Simplifications
