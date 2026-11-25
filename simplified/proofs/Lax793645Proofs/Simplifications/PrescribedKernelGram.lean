import Lax793645Proofs.Simplifications.LinearRelationFourier
import Lax793645Proofs.Simplifications.InjectivityPolynomial

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J R S U : Type}
  [Fintype I] [Fintype J] [Fintype R] [Fintype S] [Fintype U]
  [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S] [DecidableEq U]

omit [Fintype U] [DecidableEq I] [DecidableEq R] [DecidableEq U] in
theorem quotient_matrix_injective (L : Mat R I) (hL : Surjective L.mulVec) :
    Injective (rmult U L) := by
  intro X Y h
  apply coe_mv_inj
  change X.mulVecLin=Y.mulVecLin
  apply LinearMap.ext
  intro x
  obtain ⟨v,hv⟩ := hL x
  change X*ᵥx=Y*ᵥx
  rw [←hv,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  exact congrArg (fun P : Mat U I=>P*ᵥv) h

omit [Fintype U] [DecidableEq I] [DecidableEq U] in
theorem factor_through_quotient (L : Mat R I) (P : Mat U I)
    (h : LinearMap.ker L.mulVecLin≤LinearMap.ker P.mulVecLin) :
    ∃ X : Mat U R,X*L=P := by
  obtain ⟨f,hf⟩ := mem_range_comp h
  refine ⟨LinearMap.toMatrix' f,?_⟩
  apply coe_mv_inj
  change ((LinearMap.toMatrix' f)*L).mulVecLin=P.mulVecLin
  rw [Matrix.mulVecLin_mul,toMat_map]
  exact hf

omit [Fintype U] [DecidableEq I] [DecidableEq R] [DecidableEq U] in
theorem exact_kernel_mul_iff (L : Mat R I) (hL : Surjective L.mulVec) (X : Mat U R) :
    LinearMap.ker (X*L).mulVecLin=LinearMap.ker L.mulVecLin ↔ Injective X.mulVec := by
  constructor
  · intro hk
    rw [←Matrix.coe_mulVecLin,←LinearMap.ker_eq_bot]
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨v,hv⟩ := hL x
    have hz : v∈LinearMap.ker (X*L).mulVecLin := by
      change (X*L)*ᵥv=0
      rw [←Matrix.mulVec_mulVec,hv]
      exact hx
    rw [hk] at hz
    change x=0
    exact hv.symm.trans hz
  · intro hX
    ext v
    change (X*L)*ᵥv=0 ↔ L*ᵥv=0
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_zero X,hX.eq_iff]

omit [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S] [DecidableEq U] in
theorem quotient_gram_iff (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec)
    (X : Mat U R) (Y : Mat U S) (G : Mat R S) :
    (X*L)ᵀ*(Y*M)=Lᵀ*G*M ↔ Xᵀ*Y=G := by
  constructor
  · intro h
    have hLT : Injective Lᵀ.mulVec := transpose_surj_iff.mp (by rwa [transpose_transpose])
    simp only [Matrix.transpose_mul,Matrix.mul_assoc] at h
    have hh := matrix_cancel_left hLT _ _ h
    rw [←Matrix.mul_assoc] at hh
    exact quotient_matrix_injective M hM hh
  · intro h
    rw [Matrix.transpose_mul,Matrix.mul_assoc,←Matrix.mul_assoc Xᵀ,h,
      ←Matrix.mul_assoc]

def prescribedKernelGram (L : Mat R I) (M : Mat S J) (G : Mat R S)
    (z : Mat U I×Mat U J) : Prop :=
  LinearMap.ker z.1.mulVecLin=LinearMap.ker L.mulVecLin ∧
  LinearMap.ker z.2.mulVecLin=LinearMap.ker M.mulVecLin ∧ z.1ᵀ*z.2=Lᵀ*G*M

/-- The original columns and all their relations are retained. The quotient
is used solely to count the exact-kernel normalization. -/
def prescribedKernelEquiv (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S) :
    {z : Mat U R×Mat U S // gramGood G z}≃
      {z : Mat U I×Mat U J // prescribedKernelGram L M G z} := by
  classical
  let f (z : {z : Mat U R×Mat U S // gramGood G z}) :
      {z : Mat U I×Mat U J // prescribedKernelGram L M G z} :=
    ⟨(z.val.1*L,z.val.2*M),(exact_kernel_mul_iff L hL _).mpr z.property.2.1,
      (exact_kernel_mul_iff M hM _).mpr z.property.2.2,
      (quotient_gram_iff L M hL hM _ _ G).mpr z.property.1⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro z w h
    apply Subtype.ext
    apply Prod.ext
    · exact quotient_matrix_injective L hL (congrArg (fun x=>x.val.1) h)
    · exact quotient_matrix_injective M hM (congrArg (fun x=>x.val.2) h)
  · intro z
    obtain ⟨X,hX⟩ := factor_through_quotient L z.val.1 z.property.1.ge
    obtain ⟨Y,hY⟩ := factor_through_quotient M z.val.2 z.property.2.1.ge
    have hXi : Injective X.mulVec := (exact_kernel_mul_iff L hL X).mp (hX ▸ z.property.1)
    have hYi : Injective Y.mulVec := (exact_kernel_mul_iff M hM Y).mp (hY ▸ z.property.2.1)
    have hG : Xᵀ*Y=G := (quotient_gram_iff L M hL hM X Y G).mp (by
      rw [hX,hY]
      exact z.property.2.2)
    refine ⟨⟨(X,Y),hG,hXi,hYi⟩,?_⟩
    apply Subtype.ext
    exact Prod.ext hX hY

/-- Exact normalization factor, including arbitrary prescribed nominal
dependencies. It contains no change of the original Gram mask. -/
theorem prescribed_kernel_gram_mass (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S) :
    pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (prescribedKernelGram L M G)=
      bp (num U*(num R+num S-num I-num J))*
        pr (pairW unif unif : Wgt (Mat U R×Mat U S)) (gramGood G) := by
  classical
  have hn : nbr (prescribedKernelGram (U:=U) L M G)=
      nbr (gramGood (U:=U) G) := by
    rw [nbr_eq_card,nbr_eq_card]
    exact_mod_cast Fintype.card_congr (prescribedKernelEquiv (U:=U) L M hL hM G).symm
  rw [←pair_unif,←pair_unif,pr_unif,pr_unif,hn]
  simp only [Fintype.card_prod,Nat.cast_mul]
  change _/(num (Mat U I)*num (Mat U J))=
    _*(_/(num (Mat U R)*num (Mat U S)))
  rw [cast_mat,cast_mat,cast_mat,cast_mat,←bp_add,←bp_add]
  have he : num U*(num R+num S-num I-num J)=
      (num U*num R+num U*num S)-(num U*num I+num U*num J) := by ring
  rw [he,bp_sub]
  have hbp (x : ℝ) : bp x≠0 := (bp_pos x).ne'
  field_simp [hbp]

theorem prescribed_kernel_gram_lower (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S)
    (hroom : num R+num S-num U≤-1) :
    bp (num U*(num R+num S-num I-num J)-num R*num S)/4≤
      pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (prescribedKernelGram L M G) := by
  rw [prescribed_kernel_gram_mass L M hL hM G,bp_sub]
  have hh := mul_le_mul_of_nonneg_left (gram_injective_lower (U:=U) G hroom)
    (bp_pos (num U*(num R+num S-num I-num J))).le
  rw [neg_mul,bp_neg] at hh
  simpa only [div_eq_mul_inv,mul_assoc] using hh

theorem original_gram_expansion_cost (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S)
    (hroom : num R+num S-num U≤-1) :
    bp (-num I*num J)/
      pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (prescribedKernelGram L M G)≤
      4*bp (num U*(num I+num J-num R-num S)) := by
  have hR : num R≤num I := by exact_mod_cast
    (show Fintype.card R≤Fintype.card I from (mrk_surj.mp hL).symm.le.trans L.rank_le_card_width)
  have hS : num S≤num J := by exact_mod_cast
    (show Fintype.card S≤Fintype.card J from (mrk_surj.mp hM).symm.le.trans M.rank_le_card_width)
  have hprod : num R*num S≤num I*num J := mul_le_mul hR hS
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine (div_le_div₀ (bp_pos _).le le_rfl
    (div_pos (bp_pos _) (by norm_num))
    (prescribed_kernel_gram_lower L M hL hM G hroom)).trans ?_
  calc
    _=4*bp (-num I*num J-
      (num U*(num R+num S-num I-num J)-num R*num S)) := by
      have hc (x y : ℝ) : x/(y/4)=4*(x/y) := by ring
      rw [hc,←bp_sub]
    _≤_ := mul_le_mul_of_nonneg_left (bp_le (by nlinarith)) (by norm_num)

omit [Fintype U] [DecidableEq I] [DecidableEq R] [DecidableEq U] in
theorem quotient_rank (L : Mat R I) (hL : Surjective L.mulVec) (X : Mat U R) :
    (X*L).rank=X.rank := by
  change rk (X*L).mulVecLin=rk X.mulVecLin
  rw [Matrix.mulVecLin_mul]
  unfold rk
  rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hL,Submodule.map_top]

omit [DecidableEq U] in
/-- Divide out only the prescribed kernel cardinality. The polynomial is
still evaluated on the original columns. -/
theorem scaled_kernel_count (L : Mat R I) (hL : Surjective L.mulVec) (X : Mat U R) :
    bp (num R-num I)*binaryKernelCount (X*L)=binaryKernelCount X := by
  have hRI : Fintype.card R≤Fintype.card I :=
    (mrk_surj.mp hL).symm.le.trans L.rank_le_card_width
  have hXI := X.rank_le_card_width.trans hRI
  rw [binary_kernel_count,binary_kernel_count,quotient_rank L hL,
    ←bp_add,Nat.cast_sub hXI,Nat.cast_sub X.rank_le_card_width]
  congr 1
  unfold num
  ring

def relativeKernelSieve (R S : Type) [Fintype R] [Fintype S] (d : ℕ)
    (z : Mat U I×Mat U J) : ℝ :=
  kernelSieve d (bp (num R-num I)*binaryKernelCount z.1)*
    kernelSieve d (bp (num S-num J)*binaryKernelCount z.2)

omit [DecidableEq U] in
theorem relative_sieve_quotient (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec)
    (d : ℕ) (z : Mat U R×Mat U S) :
    relativeKernelSieve R S d (z.1*L,z.2*M)=pairKernelSieve d z := by
  simp only [relativeKernelSieve,scaled_kernel_count L hL,scaled_kernel_count M hM,pairKernelSieve]

omit [DecidableEq R] [DecidableEq S] in
/-- The relative polynomial has a Fourier cost depending on the surviving
nominal dimensions, without deleting any original query columns. -/
theorem relative_sieve_fourier_norm {D : Type} [Fintype D] [DecidableEq D]
    (P : Vec D→ₗ[F] Mat U I) (Q : Vec D→ₗ[F] Mat U J) (d : ℕ) :
    fourierNorm (fun x=>relativeKernelSieve R S d (P x,Q x))≤kernelSieveCost R S d := by
  have hP : fourierNorm (fun x=>bp (num R-num I)*binaryKernelCount (P x))≤bp (num R) := by
    rw [fourier_norm_smul,abs_of_pos (bp_pos _)]
    exact (mul_le_mul_of_nonneg_left (fourier_norm_kernel_count P) (bp_pos _).le).trans_eq
      (by rw [←bp_add]; congr 1; ring)
  have hQ : fourierNorm (fun x=>bp (num S-num J)*binaryKernelCount (Q x))≤bp (num S) := by
    rw [fourier_norm_smul,abs_of_pos (bp_pos _)]
    exact (mul_le_mul_of_nonneg_left (fourier_norm_kernel_count Q) (bp_pos _).le).trans_eq
      (by rw [←bp_add]; congr 1; ring)
  exact (fourier_norm_mul _ _).trans (mul_le_mul
    (fourier_norm_sieve _ d _ hP) (fourier_norm_sieve _ d _ hQ)
    (fourier_norm_nonneg _) (pow_nonneg (by linarith [bp_pos (num R)]) _))

/-- After normalizing at the prescribed nominal kernels, the image-kernel
tail has no factor charging the nominal deficiency a second time. -/
theorem relative_sieve_gram_error (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S)
    (hroom : num R+num S-num U≤-1)
    (f : Wgt (Mat U I×Mat U J)) (hf : ∀ z,|f z|≤1) (d : ℕ) :
    |avg (onW (pairW unif unif : Wgt (Mat U R×Mat U S)) (fun z=>z.1ᵀ*z.2=G))
      (fun z=>f (z.1*L,z.2*M)*
        (ind (LinearMap.ker (z.1*L).mulVecLin=LinearMap.ker L.mulVecLin ∧
          LinearMap.ker (z.2*M).mulVecLin=LinearMap.ker M.mulVecLin)-
            relativeKernelSieve R S d (z.1*L,z.2*M)))|≤
      16*(d+2)*bp ((num R+num S+4)*d+
        ((d:ℝ)+1)*(2*(num R+num S)-num U)) := by
  simp_rw [exact_kernel_mul_iff L hL,exact_kernel_mul_iff M hM,
    relative_sieve_quotient L M hL hM]
  exact gram_sieve_error_exponential G hroom (fun z=>f (z.1*L,z.2*M)) (fun z=>hf _) d

/-- Conditioning commutes with the image law, including zero-mass events. -/
theorem map_condition {A B : Type} [Fintype A] [Fintype B]
    (μ : Wgt A) (f : A→B) (p : B→Prop) :
    mapW (onW μ (p ∘ f)) f=onW (mapW μ f) p := by
  funext y
  rw [mapW,pr_on,onW_val,mapW_pr]
  congr 1
  change pr μ (fun x=>p (f x) ∧ f x=y)=pr μ (fun x=>f x=y)*ind (p y)
  simp only [pr,avg,ind_and,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x=y
  · simp only [h,ind_true,mul_one]
  · simp only [ind_zero h,mul_zero,zero_mul]

def relationGram (L : Mat R I) (M : Mat S J) (G : Mat R S)
    (z : Mat U I×Mat U J) : Prop :=
  (LinearMap.ker L.mulVecLin≤LinearMap.ker z.1.mulVecLin ∧
    LinearMap.ker M.mulVecLin≤LinearMap.ker z.2.mulVecLin) ∧ z.1ᵀ*z.2=Lᵀ*G*M

/-- The quotient sampling law is exactly the law of the original columns
conditioned on the nominal relations and all original Gram equations. -/
theorem quotient_gram_law (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S) :
    mapW (onW (pairW unif unif : Wgt (Mat U R×Mat U S)) (fun z=>z.1ᵀ*z.2=G))
      (fun z=>(z.1*L,z.2*M))=unifOn (relationGram L M G) := by
  let T := (rmult U L).prodMap (rmult U M)
  let p (z : Mat U I×Mat U J) :=
    LinearMap.ker L.mulVecLin≤LinearMap.ker z.1.mulVecLin ∧
    LinearMap.ker M.mulVecLin≤LinearMap.ker z.2.mulVecLin
  have hr : (fun z=>z∈LinearMap.range T)=p := by
    funext z
    apply propext
    constructor
    · rintro ⟨⟨X,Y⟩,h⟩
      rcases Prod.ext_iff.mp h with ⟨hX,hY⟩
      change X*L=z.1 at hX
      change Y*M=z.2 at hY
      constructor
      · intro v hv
        change z.1*ᵥv=0
        rw [←hX,←Matrix.mulVec_mulVec]
        change X*ᵥ(L*ᵥv)=0
        rw [show L*ᵥv=0 from hv,Matrix.mulVec_zero]
      · intro v hv
        change z.2*ᵥv=0
        rw [←hY,←Matrix.mulVec_mulVec]
        change Y*ᵥ(M*ᵥv)=0
        rw [show M*ᵥv=0 from hv,Matrix.mulVec_zero]
    · intro hz
      obtain ⟨X,hX⟩ := factor_through_quotient L z.1 hz.1
      obtain ⟨Y,hY⟩ := factor_through_quotient M z.2 hz.2
      exact ⟨(X,Y),Prod.ext hX hY⟩
  have hμ : mapW unif T=unifOn p := by rw [unif_lin,hr]
  have he : (fun z : Mat U R×Mat U S=>z.1ᵀ*z.2=G)=
      (fun z : Mat U I×Mat U J=>z.1ᵀ*z.2=Lᵀ*G*M) ∘ T := by
    funext z
    exact propext (quotient_gram_iff L M hL hM z.1 z.2 G).symm
  rw [←pair_unif,he]
  change mapW (onW unif (_ ∘ T)) T=_
  rw [map_condition,hμ,unifOn_and]
  rfl

/-- Relative image-kernel tail, now on the original-column conditional law.
All original Gram equations and all query batches remain present. -/
theorem original_columns_sieve_error (L : Mat R I) (M : Mat S J)
    (hL : Surjective L.mulVec) (hM : Surjective M.mulVec) (G : Mat R S)
    (hroom : num R+num S-num U≤-1)
    (f : Wgt (Mat U I×Mat U J)) (hf : ∀ z,|f z|≤1) (d : ℕ) :
    |avg (unifOn (relationGram L M G))
      (fun z=>f z*(ind (LinearMap.ker z.1.mulVecLin=LinearMap.ker L.mulVecLin ∧
          LinearMap.ker z.2.mulVecLin=LinearMap.ker M.mulVecLin)-
            relativeKernelSieve R S d z))|≤
      16*(d+2)*bp ((num R+num S+4)*d+
        ((d:ℝ)+1)*(2*(num R+num S)-num U)) := by
  rw [←quotient_gram_law L M hL hM G,mapW_avg]
  exact relative_sieve_gram_error L M hL hM G hroom f hf d

end
end Lax793645Proofs.Simplifications
