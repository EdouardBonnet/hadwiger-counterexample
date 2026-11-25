import Lax793645Proofs.Simplifications.ProductKernelComparison
import Lax793645Proofs.Simplifications.DependentFrameImages

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {D I R U G : Type}
  [Fintype D] [Fintype I] [Fintype R] [Fintype U] [Fintype G]
  [DecidableEq D] [DecidableEq I] [DecidableEq R] [DecidableEq U] [DecidableEq G]

/-- Prescribed kernels may be imposed directly on original columns. -/
theorem kernel_containment_fourier_norm (P : Vec D→ₗ[F] Mat U I)
    (S : Submodule F (Vec I)) :
    fourierNorm (fun x=>ind (S≤LinearMap.ker (P x).mulVecLin))=1 := by
  classical
  let T (v : S) : Vec D→ₗ[F] Vec U := ((Matrix.mulVecBilin F F).flip v.val).comp P
  have he x : (S≤LinearMap.ker (P x).mulVecLin) ↔ ∀ v:S,T v x=0 := by
    constructor
    · intro h v
      exact h v.property
    · intro h v hv
      exact h ⟨v,hv⟩
  simp only [he]
  exact fourier_norm_relation_family T

omit [DecidableEq R] [DecidableEq U] in
/-- Pointwise sieve growth is controlled by surviving nominal dimensions. -/
theorem relative_sieve_bound (d : ℕ) (z : Mat U I×Mat U I) :
    |relativeKernelSieve R R d z|≤kernelSieveCost R R d := by
  have hscaled (P : Mat U I) :
      0≤bp (num R-num I)*binaryKernelCount P ∧
      bp (num R-num I)*binaryKernelCount P≤bp (num R) := by
    refine ⟨mul_nonneg (bp_pos _).le (binary_kernel_count_bounds P).1,?_⟩
    refine (mul_le_mul_of_nonneg_left (binary_kernel_count_bounds P).2 (bp_pos _).le).trans_eq ?_
    rw [←bp_add]
    congr 1
    ring
  unfold relativeKernelSieve kernelSieveCost
  rw [abs_mul]
  exact mul_le_mul (kernel_sieve_bound d _ _ (hscaled z.1).1 (hscaled z.1).2)
    (kernel_sieve_bound d _ _ (hscaled z.2).1 (hscaled z.2).2) (abs_nonneg _)
    (pow_nonneg (by linarith [bp_pos (num R)]) _)

omit [DecidableEq R] in
theorem sieve_cost_ge_one (d : ℕ) : 1≤kernelSieveCost R R d := by
  unfold kernelSieveCost
  have h : (1:ℝ)≤(2+bp (num R))^d := one_le_pow₀ (by linarith [bp_pos (num R)])
  nlinarith

theorem product_coordinate_average {A : G→Type} [∀ i,Fintype (A i)]
    (μ : ∀ i,Wgt (A i)) (hμ : ∀ i,IsLaw (μ i)) (i : G) (f : Wgt (A i)) :
    avg (prodW μ) (fun x=>f (x i))=avg (μ i) f := by
  classical
  let v : ∀ j,Wgt (A j):=Function.update (fun _ _=>1) i f
  have he x : prodW v x=f (x i) := by
    unfold prodW
    rw [Finset.prod_eq_single i]
    · simp [v]
    · intro j _ hj
      simp [v,hj]
    · simp
  rw [show (fun x=>f (x i))=prodW v from (funext he).symm,prodW_avg]
  rw [Finset.prod_eq_single i]
  · simp [v]
  · intro j _ hj
    simp only [v,Function.update_of_ne hj]
    exact (hμ j).avg_const 1
  · simp

theorem original_relation_law (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hroom : 2*num R-num U≤-1) :
    IsLaw (unifOn (relationGram (U:=U) L L Q)) := by
  have hr : num R+num R-num U≤-1 := by linarith
  have hp : 0<pr (pairW unif unif : Wgt (Mat U R×Mat U R)) (fun z=>z.1ᵀ*z.2=Q) :=
    (div_pos (bp_pos _) (by norm_num)).trans_le (gram_unrestricted_lower Q hr)
  have hh := mapW_law (on_law (pairW_law unif_law unif_law).nz hp)
    (fun z : Mat U R×Mat U R=>(z.1*L,z.2*L))
  rwa [quotient_gram_law L L hL hL Q] at hh

/-- Exact image kernels retain a fixed fraction of the relation-and-Gram law. -/
theorem original_exact_kernel_mass (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hroom : 2*num R-num U≤-1) :
    (1:ℝ)/8≤pr (unifOn (relationGram (U:=U) L L Q)) (fun z=>
      LinearMap.ker z.1.mulVecLin=LinearMap.ker L.mulVecLin ∧
      LinearMap.ker z.2.mulVecLin=LinearMap.ker L.mulVecLin) := by
  rw [←quotient_gram_law L L hL hL Q,mapW_pr]
  simp only [exact_kernel_mul_iff L hL]
  exact gram_conditioned_injective_mass Q (by linarith)

variable {K H : G→Type} [∀ i,Fintype (K i)] [∀ i,Fintype (H i)]
  [∀ i,DecidableEq (K i)] [∀ i,DecidableEq (H i)]

def relationProductLaw (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i)) :
    Wgt (∀ i,Mat U (K i)×Mat U (K i)) :=
  prodW (fun i=>unifOn (relationGram (U:=U) (L i) (L i) (Q i)))

/-- All image-kernel polynomials can be replaced simultaneously. The
error is measured after conditioning on the nominal relations and Gram
equations, so no nominal-deficiency normalization is charged here. -/
theorem simultaneous_relative_sieve_error
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec)
    (hroom : ∀ i,2*num (H i)-num U≤-1)
    (f : Wgt (∀ i,Mat U (K i)×Mat U (K i))) (hf : ∀ x,|f x|≤1)
    (d : ℕ) (B : ℝ) (hB : 1≤B) (hc : ∀ i,kernelSieveCost (H i) (H i) d≤B) :
    |avg (relationProductLaw L Q) (fun x=>f x*
      ((∏ i,ind (LinearMap.ker (x i).1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
        LinearMap.ker (x i).2.mulVecLin=LinearMap.ker (L i).mulVecLin))-
       (∏ i,relativeKernelSieve (H i) (H i) d (x i))))|≤
      B^Fintype.card G*∑ i,16*(d+2)*bp ((2*num (H i)+4)*d+
        ((d:ℝ)+1)*(4*num (H i)-num U)) := by
  let μ i : Wgt (Mat U (K i)×Mat U (K i)):=unifOn (relationGram (L i) (L i) (Q i))
  have hμ i : IsLaw (μ i):=original_relation_law (L i) (hL i) (Q i) (hroom i)
  apply product_average_error (relationProductLaw L Q) (prodW_law hμ).nz _ _ f hf B hB
  · intro i x
    exact (show |ind _|≤(1:ℝ) by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _).trans hB
  · intro i x
    exact (relative_sieve_bound (R:=H i) d (x i)).trans (hc i)
  intro i
  change avg (prodW μ) (fun x=>|ind _-relativeKernelSieve (H i) (H i) d (x i)|)≤_
  rw [product_coordinate_average μ hμ i (fun z=>
    |ind (LinearMap.ker z.1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
      LinearMap.ker z.2.mulVecLin=LinearMap.ker (L i).mulVecLin)-relativeKernelSieve (H i) (H i) d z|)]
  apply l1_from_signed_tests
  intro w hw
  have hh:=original_columns_sieve_error (U:=U) (L i) (L i) (hL i) (hL i) (Q i)
    (by linarith [hroom i]) w hw d
  convert hh using 1
  congr 2
  ring

/-- Conditioning on all exact image kernels has only a fixed format cost. -/
theorem simultaneous_exact_kernel_mass
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec)
    (hroom : ∀ i,2*num (H i)-num U≤-1) :
    1/(8:ℝ)^Fintype.card G≤pr (relationProductLaw (U:=U) L Q) (fun x=>∀ i,
      LinearMap.ker (x i).1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
      LinearMap.ker (x i).2.mulVecLin=LinearMap.ker (L i).mulVecLin) := by
  unfold relationProductLaw
  rw [prodW_pr _ (fun i (z : Mat U (K i)×Mat U (K i))=>
    LinearMap.ker z.1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
      LinearMap.ker z.2.mulVecLin=LinearMap.ker (L i).mulVecLin)]
  have h:=Finset.prod_le_prod (s:=Finset.univ) (f:=fun _ : G=>(1:ℝ)/8)
    (fun _ _=>by norm_num) (fun i _=>original_exact_kernel_mass (L i) (hL i) (Q i) (hroom i))
  simpa only [Finset.prod_const,card_univ,div_pow,one_pow] using h

/-- Signed polynomial approximation followed by positive conditioning. -/
theorem conditioned_sieve_bound {A : Type} [Fintype A]
    (μ : Wgt A) (ok : A→Prop) (f s : Wgt A) (ε C : ℝ)
    (hC : 0<C) (hp : 1/C≤pr μ ok)
    (herr : |avg μ (fun x=>f x*(ind (ok x)-s x))|≤ε) :
    |avg (onW μ ok) f|≤C*(|avg μ (fun x=>f x*s x)|+ε) := by
  have hp' : 0<pr μ ok := (one_div_pos.mpr hC).trans_le hp
  have he : avg (subW μ ok) f=avg μ (fun x=>f x*(ind (ok x)-s x))+
      avg μ (fun x=>f x*s x) := by
    rw [←avg_add]
    unfold avg subW
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hn : |avg (subW μ ok) f|≤|avg μ (fun x=>f x*s x)|+ε := by
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  change |avg (normW (subW μ ok)) f|≤_
  rw [avg_norm,subW_tot,abs_div,abs_of_pos hp']
  apply (div_le_iff₀ hp').mpr
  have hnon : 0≤|avg μ (fun x=>f x*s x)|+ε := (abs_nonneg _).trans hn
  have hm : 1≤C*pr μ ok := by
    have hh:=mul_le_mul_of_nonneg_left hp hC.le
    rwa [mul_one_div_cancel hC.ne'] at hh
  have hh:=mul_le_mul_of_nonneg_right hm hnon
  nlinarith

/-- Simultaneous conditional version, applicable to the exact raw frame
image law after the coordinate equivalence in DependentFrameImages. -/
theorem simultaneous_conditioned_sieve
    (L : ∀ i,Mat (H i) (K i)) (Q : ∀ i,Mat (H i) (H i))
    (hL : ∀ i,Surjective (L i).mulVec)
    (hroom : ∀ i,2*num (H i)-num U≤-1)
    (f : Wgt (∀ i,Mat U (K i)×Mat U (K i))) (hf : ∀ x,|f x|≤1)
    (d : ℕ) (B : ℝ) (hB : 1≤B) (hc : ∀ i,kernelSieveCost (H i) (H i) d≤B) :
    |avg (onW (relationProductLaw L Q) (fun x=>∀ i,
      LinearMap.ker (x i).1.mulVecLin=LinearMap.ker (L i).mulVecLin ∧
      LinearMap.ker (x i).2.mulVecLin=LinearMap.ker (L i).mulVecLin)) f|≤
      (8:ℝ)^Fintype.card G*
        (|avg (relationProductLaw L Q) (fun x=>f x*∏ i,relativeKernelSieve (H i) (H i) d (x i))|+
         B^Fintype.card G*∑ i,16*(d+2)*bp ((2*num (H i)+4)*d+
           ((d:ℝ)+1)*(4*num (H i)-num U))) := by
  apply conditioned_sieve_bound _ _ _ _ _ _ (pow_pos (by norm_num) _)
    (simultaneous_exact_kernel_mass L Q hL hroom)
  simpa only [ind_all] using simultaneous_relative_sieve_error L Q hL hroom f hf d B hB hc

end
end Lax793645Proofs.Simplifications
