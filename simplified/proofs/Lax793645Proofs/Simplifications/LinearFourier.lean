import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def linearFourier (f : Wgt (Vec I)) (ξ : Vec I) : ℝ :=
  avg unif (fun x=>vectorPhase ξ x*f x)

theorem linear_fourier_pair (f g : Wgt (Vec I)) :
    avg unif (fun x=>f x*g x)=∑ ξ:Vec I,linearFourier f ξ*linearFourier g ξ := by
  have he (x : Vec I) : f x*g x=(∑ ξ:Vec I,linearFourier f ξ*vectorPhase ξ x)*g x := by
    simpa only [linearFourier] using congrArg (fun a=>a*g x) (hat_eqn f x).symm
  simp_rw [he,Finset.sum_mul,avg_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  unfold linearFourier
  rw [←avg_mul']
  apply avg_congr
  intro x _
  ring

theorem linear_fourier_parseval (f : Wgt (Vec I)) :
    ∑ ξ:Vec I,(linearFourier f ξ)^2=avg unif (fun x=>(f x)^2) := by
  simpa only [pow_two] using (linear_fourier_pair f f).symm

/-- Exact four-corner identity for the ambient binary Fourier transform. -/
theorem linear_fourier_four_corner (f0 f1 f2 f3 : Wgt (Vec I)) :
    avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      f0 x*f1 y*f2 z*f3 (x+y+z))))=
      ∑ ξ:Vec I,linearFourier f0 ξ*linearFourier f1 ξ*
        linearFourier f2 ξ*linearFourier f3 ξ := by
  have he (x y z : Vec I) : f3 (x+y+z)=
      ∑ ξ:Vec I,linearFourier f3 ξ*vectorPhase ξ x*vectorPhase ξ y*vectorPhase ξ z := by
    rw [←hat_eqn f3 (x+y+z)]
    apply Finset.sum_congr rfl
    intro ξ _
    simp only [linearFourier,vectorPhase,dotProduct_add,wsign_add]
    ring
  simp_rw [he,Finset.mul_sum,avg_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  have hx (x y z : Vec I) :
      f0 x*f1 y*f2 z*(linearFourier f3 ξ*vectorPhase ξ x*vectorPhase ξ y*vectorPhase ξ z)=
      (vectorPhase ξ x*f0 x)*(vectorPhase ξ y*f1 y)*(vectorPhase ξ z*f2 z)*linearFourier f3 ξ := by ring
  simp_rw [hx,avg_mul,avg_mul']
  simp_rw [avg_mul,avg_mul']
  rw [avg_mul]
  rfl

/-- Small ordinary Fourier coefficients give a small four-corner mean.
There is no ambient-dimension factor in this estimate. -/
theorem small_fourier_four_corner (f0 f1 f2 f3 : Wgt (Vec I)) (δ : ℝ) (hδ : 0≤δ)
    (h0 : ∀ ξ,|linearFourier f0 ξ|≤δ) (h1 : ∀ ξ,|linearFourier f1 ξ|≤δ)
    (h2 : ∀ x,|f2 x|≤1) (h3 : ∀ x,|f3 x|≤1) :
    |avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
      f0 x*f1 y*f2 z*f3 (x+y+z))))|≤δ^2 := by
  rw [linear_fourier_four_corner]
  have hparse (f : Wgt (Vec I)) (hf : ∀ x,|f x|≤1) :
      ∑ ξ:Vec I,(linearFourier f ξ)^2≤1 := by
    rw [linear_fourier_parseval]
    apply unif_law.avg_le
    intro x
    have hh := abs_le.mp (hf x)
    nlinarith [hh.1,hh.2]
  have hcs : ∑ ξ:Vec I,|linearFourier f2 ξ| * |linearFourier f3 ξ|≤1 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq univ
      (fun ξ=>|linearFourier f2 ξ|) (fun ξ=>|linearFourier f3 ξ|)
    simp only [sq_abs] at hh
    have hprod : (∑ ξ:Vec I,(linearFourier f2 ξ)^2)*
        (∑ ξ:Vec I,(linearFourier f3 ξ)^2)≤1 := by
      exact (mul_le_mul (hparse f2 h2) (hparse f3 h3)
        (Finset.sum_nonneg (fun _ _=>sq_nonneg _)) (by norm_num)).trans_eq (one_mul _)
    nlinarith
  calc
    _≤∑ ξ:Vec I,|linearFourier f0 ξ*linearFourier f1 ξ*
        linearFourier f2 ξ*linearFourier f3 ξ| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ ξ:Vec I,δ^2*(|linearFourier f2 ξ| * |linearFourier f3 ξ|) := by
      apply Finset.sum_le_sum
      intro ξ _
      simp only [abs_mul]
      have hh := mul_le_mul (h0 ξ) (h1 ξ) (abs_nonneg _) hδ
      calc
        _=(|linearFourier f0 ξ| * |linearFourier f1 ξ|)*
            (|linearFourier f2 ξ| * |linearFourier f3 ξ|) := by ring
        _≤_ := mul_le_mul_of_nonneg_right (by simpa only [pow_two] using hh)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _≤δ^2 := by rw [←Finset.mul_sum]; nlinarith [sq_nonneg δ]

end
end Lax793645Proofs.Simplifications
