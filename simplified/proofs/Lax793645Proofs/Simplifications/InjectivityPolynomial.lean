import Lax793645Proofs.Simplifications.FourierNorm
import Lax793645Proofs.Simplifications.GramKernelBounds

/-! # A finite injectivity polynomial

Instead of expanding over every kernel subspace, interpolate the injectivity
indicator at kernel sizes 1, 2, ..., 2^d. The resulting polynomial is exact
below the cutoff. Its Fourier norm is at most exponential in d times the
nominal column count. GramKernelBounds controls the remaining kernel tail.
This is an ingredient of the high-moment proposal, not its full assembly.
-/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A finite interpolation polynomial: one on a trivial kernel and zero on
every nontrivial kernel whose dimension is at most d. -/
def kernelSieve (d : ℕ) (t : ℝ) : ℝ :=
  ∏ j : Fin d,((2:ℝ)^(j.val+1)-t)/((2:ℝ)^(j.val+1)-1)

private theorem two_le_sieve_scale (j : ℕ) : 2≤(2:ℝ)^(j+1) := by
  have hh : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

theorem kernel_sieve_one (d : ℕ) : kernelSieve d 1=1 := by
  unfold kernelSieve
  apply Finset.prod_eq_one
  intro j _
  have hh := two_le_sieve_scale j.val
  exact div_self (by linarith)

theorem kernel_sieve_small (d k : ℕ) (hk : 0<k) (hkd : k≤d) :
    kernelSieve d ((2:ℝ)^k)=0 := by
  classical
  let j : Fin d := ⟨k-1,by omega⟩
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  have he : j.val+1=k := by dsimp [j]; omega
  rw [he,sub_self,zero_div]

theorem kernel_sieve_succ (d : ℕ) (t : ℝ) :
    kernelSieve (d+1) t=kernelSieve d t*
      (((2:ℝ)^(d+1)-t)/((2:ℝ)^(d+1)-1)) := by
  simp only [kernelSieve,Fin.prod_univ_castSucc,Fin.val_castSucc,Fin.val_last]

private theorem sieve_fraction_bound (a B : ℝ) (ha : 2≤a) (hB : 0≤B) :
    (a+B)/(a-1)≤2+B := by
  apply (div_le_iff₀ (by linarith)).mpr
  nlinarith [mul_nonneg hB (show 0≤a-2 by linarith)]

theorem kernel_sieve_bound (d : ℕ) (t B : ℝ) (ht : 0≤t) (htB : t≤B) :
    |kernelSieve d t|≤(2+B)^d := by
  have hB : 0≤B := ht.trans htB
  unfold kernelSieve
  rw [Finset.abs_prod]
  calc
    _≤∏ j : Fin d,(2+B) := by
      apply Finset.prod_le_prod (fun _ _=>abs_nonneg _)
      intro j _
      have ha := two_le_sieve_scale j.val
      rw [abs_div,abs_of_nonneg (show 0≤(2:ℝ)^(j.val+1)-1 by linarith)]
      have habs : |(2:ℝ)^(j.val+1)-t|≤(2:ℝ)^(j.val+1)+B :=
        (abs_sub _ _).trans (by
          rw [abs_of_nonneg (by positivity),abs_of_nonneg ht]
          exact add_le_add_right htB _)
      apply (div_le_div_of_nonneg_right habs
        (show 0≤(2:ℝ)^(j.val+1)-1 by linarith)).trans
      exact sieve_fraction_bound _ B ha hB
    _=_ := by simp

variable {I : Type} [Fintype I] [DecidableEq I]

theorem fourier_norm_sieve (K : Wgt (Vec I)) (d : ℕ) (B : ℝ)
    (hK : fourierNorm K≤B) :
    fourierNorm (fun x=>kernelSieve d (K x))≤(2+B)^d := by
  have hB : 0≤B := (fourier_norm_nonneg K).trans hK
  have hfactor (j : ℕ) :
      fourierNorm (fun x=>((2:ℝ)^(j+1)-K x)/((2:ℝ)^(j+1)-1))≤2+B := by
    let a : ℝ := (2:ℝ)^(j+1)
    have ha : 2≤a := two_le_sieve_scale j
    have he : (fun x=> (a-K x)/(a-1))=(fun x=>(a-1)⁻¹*(a+(-1)*K x)) := by
      ext x
      ring
    change fourierNorm (fun x=> (a-K x)/(a-1))≤_
    rw [he,fourier_norm_smul,abs_of_pos (inv_pos.mpr (by linarith))]
    refine (mul_le_mul_of_nonneg_left (fourier_norm_add (fun _=>a) (fun x=>(-1)*K x))
      (inv_nonneg.mpr (by linarith))).trans ?_
    rw [fourier_norm_const,abs_of_nonneg (by linarith : 0≤a),fourier_norm_smul]
    norm_num only [abs_neg,abs_one,one_mul]
    calc
      _≤(a-1)⁻¹*(a+B) := mul_le_mul_of_nonneg_left (add_le_add_right hK a)
        (inv_nonneg.mpr (by linarith))
      _=(a+B)/(a-1) := by ring
      _≤_ := sieve_fraction_bound a B ha hB
  induction d with
  | zero => simp only [kernelSieve,Finset.univ_eq_empty,Finset.prod_empty,
      fourier_norm_const,abs_one,pow_zero,le_refl]
  | succ d ih =>
    simp_rw [kernel_sieve_succ]
    refine (fourier_norm_mul _ _).trans ?_
    have hh := mul_le_mul ih (hfactor d) (fourier_norm_nonneg _)
      (pow_nonneg (by linarith : 0≤2+B) d)
    simpa only [pow_succ] using hh

def binaryKernelCount {U : Type} [Fintype U] (P : Mat U I) : ℝ :=
  nbr (fun v : Vec I=>P*ᵥv=0)

theorem binary_kernel_count {U : Type} [Fintype U] (P : Mat U I) :
    binaryKernelCount P=bp ((Fintype.card I-P.rank:ℕ):ℝ) := by
  classical
  change nbr (fun v=>v∈LinearMap.ker P.mulVecLin)=_
  rw [nbr_eq_card,card_space]
  congr 1
  have hh := P.mulVecLin.finrank_range_add_finrank_ker
  change P.rank+dim (LinearMap.ker P.mulVecLin)=dim (Vec I) at hh
  rw [dim_vec] at hh
  congr 1
  omega

theorem binary_kernel_count_bounds {U : Type} [Fintype U] (P : Mat U I) :
    0≤binaryKernelCount P ∧ binaryKernelCount P≤bp (num I) := by
  rw [binary_kernel_count]
  refine ⟨(bp_pos _).le,bp_le ?_⟩
  exact_mod_cast Nat.sub_le (Fintype.card I) P.rank

theorem fourier_norm_kernel_count {U D : Type} [Fintype U] [Fintype D]
    [DecidableEq U] [DecidableEq D] (P : Vec D→ₗ[F] Mat U I) :
    fourierNorm (fun x=>binaryKernelCount (P x))≤bp (num I) := by
  classical
  have hterm (v : Vec I) : fourierNorm (fun x=>ind ((P x)*ᵥv=0))≤1 := by
    let T : Vec D→ₗ[F] Vec U := ((Matrix.mulVecBilin F F).flip v).comp P
    have he (x : Vec D) : (LinearMap.toMatrix' T)*ᵥx=(P x)*ᵥv :=
      LinearMap.congr_fun (toMat_map T) x
    simpa only [he] using fourier_norm_kernel (LinearMap.toMatrix' T)
  change fourierNorm (fun x=>∑ v:Vec I,ind ((P x)*ᵥv=0))≤_
  refine (fourier_norm_sum _).trans ((Finset.sum_le_sum (fun v _=>hterm v)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,card_space,dim_vec,num]

theorem matrix_sieve_exact {U : Type} [Fintype U] (P : Mat U I) (d : ℕ)
    (hd : Fintype.card I-P.rank≤d) :
    kernelSieve d (binaryKernelCount P)=ind (Injective P.mulVec) := by
  classical
  rw [binary_kernel_count,bp_nat]
  by_cases hP : Injective P.mulVec
  · rw [mrk_inj.mp hP,Nat.sub_self,pow_zero,kernel_sieve_one,ind_one hP]
  · rw [ind_zero hP]
    apply kernel_sieve_small _ _ _ hd
    have hle := P.rank_le_card_width
    have hne : P.rank≠Fintype.card I := fun he=>hP (mrk_inj.mpr he)
    omega

variable {J U : Type} [Fintype J] [Fintype U] [DecidableEq J] [DecidableEq U]

def pairKernelSieve (d : ℕ) (z : Mat U I×Mat U J) : ℝ :=
  kernelSieve d (binaryKernelCount z.1)*kernelSieve d (binaryKernelCount z.2)

def kernelSieveCost (I J : Type) [Fintype I] [Fintype J] (d : ℕ) : ℝ :=
  (2+bp (num I))^d*(2+bp (num J))^d

omit [DecidableEq U] in
theorem pair_kernel_sieve_bound (d : ℕ) (z : Mat U I×Mat U J) :
    |pairKernelSieve d z|≤kernelSieveCost I J d := by
  unfold pairKernelSieve kernelSieveCost
  rw [abs_mul]
  exact mul_le_mul
    (kernel_sieve_bound d _ _ (binary_kernel_count_bounds z.1).1 (binary_kernel_count_bounds z.1).2)
    (kernel_sieve_bound d _ _ (binary_kernel_count_bounds z.2).1 (binary_kernel_count_bounds z.2).2)
    (abs_nonneg _) (pow_nonneg (by linarith [bp_pos (num I)]) _)

theorem fourier_norm_pair_sieve {D : Type} [Fintype D] [DecidableEq D]
    (P : Vec D→ₗ[F] Mat U I) (Q : Vec D→ₗ[F] Mat U J) (d : ℕ) :
    fourierNorm (fun x=>pairKernelSieve d (P x,Q x))≤kernelSieveCost I J d := by
  refine (fourier_norm_mul _ _).trans ?_
  exact mul_le_mul
    (fourier_norm_sieve _ d _ (fourier_norm_kernel_count P))
    (fourier_norm_sieve _ d _ (fourier_norm_kernel_count Q))
    (fourier_norm_nonneg _) (pow_nonneg (by linarith [bp_pos (num I)]) _)

omit [DecidableEq U] in
theorem pair_kernel_sieve_exact (d : ℕ) (z : Mat U I×Mat U J)
    (hd : (Fintype.card I-z.1.rank)+(Fintype.card J-z.2.rank)≤d) :
    pairKernelSieve d z=ind (Injective z.1.mulVec ∧ Injective z.2.mulVec) := by
  rw [pairKernelSieve,matrix_sieve_exact z.1 d (by omega),
    matrix_sieve_exact z.2 d (by omega),ind_and]

/-- Finite polynomial replacement of the injectivity indicator under a Gram
law. The error is confined to high kernel dimension; all other terms have
the controlled Fourier norm given above. -/
theorem gram_sieve_error (G : Mat I J) (hroom : num I+num J-num U≤-1)
    (f : Wgt (Mat U I×Mat U J)) (hf : ∀ z,|f z|≤1) (d : ℕ) :
    |avg (onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G))
      (fun z=>f z*(ind (Injective z.1.mulVec ∧ Injective z.2.mulVec)-pairKernelSieve d z))|≤
      (kernelSieveCost I J d+1)*(8*(d+2)*
        bp (((d:ℝ)+1)*(2*(num I+num J)-num U))) := by
  classical
  let W := onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G)
  let bad (z : Mat U I×Mat U J) := d+1≤(Fintype.card I-z.1.rank)+(Fintype.card J-z.2.rank)
  have hW : ∀ z,0≤W z := normW_nonneg
    (subW_nonneg (pairW_law unif_law unif_law).nz _)
  have hC : 0≤kernelSieveCost I J d := by
    unfold kernelSieveCost
    exact mul_nonneg (pow_nonneg (by linarith [bp_pos (num I)]) _)
      (pow_nonneg (by linarith [bp_pos (num J)]) _)
  have hpoint (z : Mat U I×Mat U J) :
      |f z*(ind (Injective z.1.mulVec ∧ Injective z.2.mulVec)-pairKernelSieve d z)|≤
        (kernelSieveCost I J d+1)*ind (bad z) := by
    by_cases hz : bad z
    · rw [ind_one hz,mul_one,abs_mul]
      refine (mul_le_mul_of_nonneg_right (hf z) (abs_nonneg _)).trans ?_
      rw [one_mul]
      have hi : |ind (Injective z.1.mulVec ∧ Injective z.2.mulVec)|≤1 := by
        rw [abs_of_nonneg (ind_nonneg _)]
        exact ind_le_one _
      exact (abs_sub _ _).trans (by linarith [pair_kernel_sieve_bound d z])
    · have hd : (Fintype.card I-z.1.rank)+(Fintype.card J-z.2.rank)≤d := by
        dsimp [bad] at hz
        omega
      rw [pair_kernel_sieve_exact d z hd,sub_self,mul_zero,abs_zero,ind_zero hz,mul_zero]
  refine ((abs_avg_le hW).trans (avg_mono hW hpoint)).trans ?_
  rw [avg_mul']
  exact mul_le_mul_of_nonneg_left
    (by
      change pr W bad≤_
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two]
        using gram_conditioned_kernel_tail (U:=U) G hroom (d+1))
    (by linarith : 0≤kernelSieveCost I J d+1)

omit [DecidableEq I] [DecidableEq J] in
/-- The Fourier cost grows exponentially in the number of nominal columns,
with a coefficient depending on the fixed cutoff d, not on ambient dimension. -/
theorem kernel_sieve_cost_exponential (d : ℕ) :
    kernelSieveCost I J d≤bp ((num I+num J+4)*d) := by
  have hsingle (A : Type) [Fintype A] : (2+bp (num A))^d≤bp ((num A+2)*d) := by
    rw [bp_mul_nat]
    apply pow_le_pow_left₀ (by linarith [bp_pos (num A)])
    have h1 : 1≤bp (num A) := by
      rw [←bp_zero]
      exact bp_le (Nat.cast_nonneg _)
    have hb2 : bp 2=4 := by
      rw [show (2:ℝ)=1+1 by norm_num,bp_add,bp_one]
      norm_num
    rw [bp_add,hb2]
    linarith
  refine (mul_le_mul (hsingle I) (hsingle J)
    (pow_nonneg (by linarith [bp_pos (num J)]) _) (bp_pos _).le).trans_eq ?_
  rw [←bp_add]
  congr 1
  ring

theorem gram_sieve_error_exponential (G : Mat I J)
    (hroom : num I+num J-num U≤-1)
    (f : Wgt (Mat U I×Mat U J)) (hf : ∀ z,|f z|≤1) (d : ℕ) :
    |avg (onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G))
      (fun z=>f z*(ind (Injective z.1.mulVec ∧ Injective z.2.mulVec)-pairKernelSieve d z))|≤
      16*(d+2)*bp ((num I+num J+4)*d+
        ((d:ℝ)+1)*(2*(num I+num J)-num U)) := by
  have h1 : 1≤bp ((num I+num J+4)*d) := by
    rw [←bp_zero]
    apply bp_le
    exact mul_nonneg (by
      have hI : 0≤num I := Nat.cast_nonneg _
      have hJ : 0≤num J := Nat.cast_nonneg _
      linarith) (Nat.cast_nonneg _)
  have hC : kernelSieveCost I J d+1≤2*bp ((num I+num J+4)*d) := by
    linarith [kernel_sieve_cost_exponential (I:=I) (J:=J) d]
  refine (gram_sieve_error G hroom f hf d).trans
    ((mul_le_mul_of_nonneg_right hC (mul_nonneg (by positivity) (bp_pos _).le)).trans_eq ?_)
  rw [bp_add]
  ring

/-- The actual injective Gram law is reduced to a Fourier-controlled
polynomial under the unrestricted Gram law and the explicit kernel tail. -/
theorem gram_injective_sieve_comparison (G : Mat I J)
    (hroom : num I+num J-num U≤-1)
    (f : Wgt (Mat U I×Mat U J)) (hf : ∀ z,|f z|≤1) (d : ℕ) :
    let W := onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G)
    |avg (onW W (fun z=>Injective z.1.mulVec ∧ Injective z.2.mulVec)) f|≤
      8*(|avg W (fun z=>f z*pairKernelSieve d z)|+
        16*(d+2)*bp ((num I+num J+4)*d+
          ((d:ℝ)+1)*(2*(num I+num J)-num U))) := by
  intro W
  let ok (z : Mat U I×Mat U J) := Injective z.1.mulVec ∧ Injective z.2.mulVec
  have hp : (1:ℝ)/8≤pr W ok := gram_conditioned_injective_mass G hroom
  have hp' : 0<pr W ok := lt_of_lt_of_le (by norm_num) hp
  have he : avg (subW W ok) f=
      avg W (fun z=>f z*(ind (ok z)-pairKernelSieve d z))+
      avg W (fun z=>f z*pairKernelSieve d z) := by
    rw [←avg_add]
    unfold avg subW
    apply Finset.sum_congr rfl
    intro z _
    ring
  have hnum : |avg (subW W ok) f|≤
      |avg W (fun z=>f z*pairKernelSieve d z)|+
        16*(d+2)*bp ((num I+num J+4)*d+
          ((d:ℝ)+1)*(2*(num I+num J)-num U)) := by
    rw [he]
    exact (abs_add_le _ _).trans (by linarith [gram_sieve_error_exponential G hroom f hf d])
  change |avg (normW (subW W ok)) f|≤_
  rw [avg_norm,subW_tot,abs_div,abs_of_pos hp']
  apply (div_le_iff₀ hp').mpr
  have hbound : 0≤|avg W (fun z=>f z*pairKernelSieve d z)|+
        16*(d+2)*bp ((num I+num J+4)*d+
          ((d:ℝ)+1)*(2*(num I+num J)-num U)) := (abs_nonneg _).trans hnum
  nlinarith [mul_le_mul_of_nonneg_right hp hbound]

end
end Lax793645Proofs.Simplifications
