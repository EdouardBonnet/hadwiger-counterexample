import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GramProbabilities
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CellPruning

/-! # Image kernels under Gram conditioning

These finite estimates support the proposed capped-leaf Fourier argument.
Dependent image frames are retained until their kernel dimensions have been
charged. No unconditional error is multiplied by a leaf cap here.
The high-moment query estimate and its application remain separate obligations.
-/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Finset Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
  [DecidableEq I] [DecidableEq J] [DecidableEq U]

omit [DecidableEq I] in
/-- A Gram fiber with a possibly dependent first frame costs its actual
rank, not its nominal number of columns. -/
theorem gram_fiber_rank_bound (P : Mat U I) (G : Mat I J) :
    pr unif (fun Q : Mat U J=>Pᵀ*Q=G)≤bp (-(P.rank:ℝ)*num J) := by
  classical
  by_cases h : ∃ Q : Mat U J,Pᵀ*Q=G
  · obtain ⟨Q₀,hQ₀⟩ := h
    obtain ⟨A,B,hA,hB,hAB⟩ := rank_product P
    have hBT : Injective Bᵀ.mulVec := by
      rw [mrk_inj,Matrix.rank_transpose,←mrk_surj]
      exact hB
    have himp (Q : Mat U J) (hQ : Pᵀ*Q=G) : Aᵀ*Q=Aᵀ*Q₀ := by
      apply matrix_cancel_left hBT
      rw [←Matrix.mul_assoc,←Matrix.transpose_mul,hAB,hQ]
      rw [←Matrix.mul_assoc,←Matrix.transpose_mul,hAB,hQ₀]
    refine (pr_mono unif_law.nz himp).trans_eq ?_
    rw [pr_gram_fixed hA]
    simp only [num,Fintype.card_fin]
  · have he : (fun Q : Mat U J=>Pᵀ*Q=G)=(fun _=>False) := by
      ext Q
      exact iff_false_intro (fun hh=>h ⟨Q,hh⟩)
    rw [he,pr_false]
    exact (bp_pos _).le

private theorem finite_binary_geometric (m : ℕ) :
    ∑ d : Fin m,bp (-(d.val:ℝ))≤2 := by
  have he (m : ℕ) : (∑ d : Fin m,bp (-(d.val:ℝ)))=2*(1-bp (-(m:ℝ))) := by
    induction m with
    | zero => simp [bp_zero]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
      rw [ih]
      rw [neg_add,bp_add,bp_neg (1:ℝ),bp_one]
      ring
  rw [he]
  linarith [bp_pos (-(m:ℝ))]

/-- Full Gram normalization without discarding dependent image frames.
This estimate is uniform over the prescribed Gram table. -/
theorem gram_unrestricted_upper (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    pr (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun x=>x.1ᵀ*x.2=G)≤2*bp (-num I*num J) := by
  classical
  let a := Fintype.card I
  let deficit (P : Mat U I) : Fin (a+1) :=
    ⟨a-P.rank,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hr (P : Mat U I) : P.rank+(deficit P).val=a :=
    Nat.add_sub_of_le P.rank_le_card_width
  have hsplit (P : Mat U I) :
      bp (-(P.rank:ℝ)*num J)=∑ d : Fin (a+1),
        ind (deficit P=d)*bp (-((a-d.val:ℕ):ℝ)*num J) := by
    rw [Finset.sum_eq_single (deficit P)]
    · rw [ind_one rfl,one_mul]
      have he : a-(deficit P).val=P.rank := by have hh := hr P; omega
      rw [he]
    · intro d _ hd
      rw [ind_zero hd.symm,zero_mul]
    · simp
  have hp (d : Fin (a+1)) : pr unif (fun P : Mat U I=>deficit P=d)≤
      bp ((num I-num U)*d.val) := by
    apply (pr_mono unif_law.nz (fun P h=>?_)).trans (pr_deficient d.val)
    have hh := hr P
    rw [h] at hh
    exact hh.le
  have hterm (d : Fin (a+1)) :
      pr unif (fun P : Mat U I=>deficit P=d)*bp (-((a-d.val:ℕ):ℝ)*num J)≤
        bp (-num I*num J)*bp (-(d.val:ℝ)) := by
    apply (mul_le_mul_of_nonneg_right (hp d) (bp_pos _).le).trans
    rw [←bp_add,←bp_add]
    apply bp_le
    have hd : d.val≤a := Nat.le_of_lt_succ d.isLt
    rw [Nat.cast_sub hd]
    have hn : (a:ℝ)=num I := rfl
    rw [hn]
    have hb := mul_le_mul_of_nonneg_right hroom (Nat.cast_nonneg d.val : (0:ℝ)≤d.val)
    nlinarith
  rw [pr,pairW_avg]
  refine (avg_mono unif_law.nz (fun P=>gram_fiber_rank_bound P G)).trans ?_
  simp_rw [hsplit,avg_sum,avg_mul]
  change (∑ d : Fin (a+1),pr unif (fun P=>deficit P=d)*_)≤_
  refine (Finset.sum_le_sum (fun d _=>hterm d)).trans ?_
  rw [←Finset.mul_sum,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (finite_binary_geometric (a+1)) (bp_pos _).le

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
private theorem factor_columns {K : Type} [Fintype K] [DecidableEq K]
    (P : Mat I J) (Q : Mat I K) (h : colSp P ≤ colSp Q) :
    ∃ R : Mat K J,Q*R=P := by
  classical
  choose f hf using fun j=>show ∃ z : Vec K,Q*ᵥz=P.col j from h (colSp_mem j)
  refine ⟨Matrix.of (fun i j=>f j i),?_⟩
  ext i j
  exact congrFun (hf j) i

/-- Uniform matrices with a prescribed image kernel are reduced uniform
matrices in a basis of its annihilator. No injectivity is assumed. -/
theorem matrix_kernel_parameterization {E : Type} [Fintype E] [DecidableEq E]
    (A : Mat I E) :
    mapW (unif : Wgt (Mat U (Fin (dim (LinearMap.ker Aᵀ.mulVecLin)))))
      (fun X=>X*(pack (LinearMap.ker Aᵀ.mulVecLin))ᵀ)=
      unifOn (fun P : Mat U I=>P*A=0) := by
  classical
  let B := pack (LinearMap.ker Aᵀ.mulVecLin)
  have hBA : Aᵀ*B=0 := by
    apply coe_mv_inj
    change (Aᵀ*B).mulVecLin=(0 : Mat E (Fin (dim (LinearMap.ker Aᵀ.mulVecLin)))).mulVecLin
    rw [Matrix.mulVecLin_mul,Matrix.mulVecLin_zero]
    apply LinearMap.ext
    intro x
    have hx : B.mulVecLin x ∈ colSp B := ⟨x,rfl⟩
    rw [show colSp B=LinearMap.ker Aᵀ.mulVecLin from colSp_pack _] at hx
    exact hx
  have he (P : Mat U I) : P∈(rmult U Bᵀ).range ↔ P*A=0 := by
    constructor
    · rintro ⟨X,rfl⟩
      change X*Bᵀ*A=0
      have hb : Bᵀ*A=0 := by
        simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero]
          using congrArg Matrix.transpose hBA
      rw [Matrix.mul_assoc,hb,Matrix.mul_zero]
    · intro hP
      have hcol : colSp Pᵀ≤colSp B := by
        rw [show colSp B=LinearMap.ker Aᵀ.mulVecLin from colSp_pack _]
        rintro _ ⟨z,rfl⟩
        change Aᵀ*ᵥ(Pᵀ*ᵥz)=0
        rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,hP,
          Matrix.transpose_zero,Matrix.zero_mulVec]
      obtain ⟨X,hX⟩ := factor_columns Pᵀ B hcol
      refine ⟨Xᵀ,?_⟩
      change Xᵀ*Bᵀ=P
      simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using
        congrArg Matrix.transpose hX
  change mapW unif (rmult U Bᵀ)=_
  rw [unif_lin]
  congr 1
  funext P
  exact propext (he P)

omit [DecidableEq I] [DecidableEq J] in
private theorem gram_embedded_upper {R S : Type}
    [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (B : Mat I R) (C : Mat J S)
    (hB : Injective B.mulVec) (hC : Injective C.mulVec) (G : Mat I J)
    (hroom : num R+num S-num U≤-1) :
    pr (pairW unif unif : Wgt (Mat U R×Mat U S))
      (fun z=>(z.1*Bᵀ)ᵀ*(z.2*Cᵀ)=G)≤2*bp (-num R*num S) := by
  classical
  by_cases h : ∃ z : Mat U R×Mat U S,(z.1*Bᵀ)ᵀ*(z.2*Cᵀ)=G
  · obtain ⟨z₀,hz₀⟩ := h
    have hh (z : Mat U R×Mat U S) (hz : (z.1*Bᵀ)ᵀ*(z.2*Cᵀ)=G) :
        z.1ᵀ*z.2=z₀.1ᵀ*z₀.2 := by
      have he := hz.trans hz₀.symm
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc] at he
      have he' := matrix_cancel_left hB _ _ he
      rw [←Matrix.mul_assoc,←Matrix.mul_assoc] at he'
      have ht := congrArg Matrix.transpose he'
      simp only [Matrix.transpose_mul,Matrix.transpose_transpose] at ht
      have ht' := matrix_cancel_left hC _ _ ht
      apply Matrix.transpose_injective
      simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using ht'
    exact (pr_mono (pairW_law unif_law unif_law).nz hh).trans
      (gram_unrestricted_upper (z₀.1ᵀ*z₀.2) hroom)
  · have he : (fun z : Mat U R×Mat U S=>(z.1*Bᵀ)ᵀ*(z.2*Cᵀ)=G)=
        (fun _=>False) := by
      ext z
      exact iff_false_intro (fun hz=>h ⟨z,hz⟩)
    rw [he,pr_false]
    exact mul_nonneg (by norm_num) (bp_pos _).le

/-- Conditioning on specified kernels reduces the nominal dimensions before
the Gram normalization is paid. -/
theorem gram_fixed_kernels_upper {E T : Type}
    [Fintype E] [Fintype T] [DecidableEq E] [DecidableEq T]
    (A : Mat I E) (C : Mat J T) (G : Mat I J)
    (hroom : (dim (LinearMap.ker Aᵀ.mulVecLin):ℝ)+
      dim (LinearMap.ker Cᵀ.mulVecLin)-num U≤-1) :
    pr (pairW (unifOn (fun P : Mat U I=>P*A=0))
      (unifOn (fun Q : Mat U J=>Q*C=0)))
      (fun z=>z.1ᵀ*z.2=G)≤
      2*bp (-(dim (LinearMap.ker Aᵀ.mulVecLin):ℝ)*dim (LinearMap.ker Cᵀ.mulVecLin)) := by
  rw [pr,pairW_avg,←matrix_kernel_parameterization A,←matrix_kernel_parameterization C]
  simp_rw [mapW_avg]
  simpa only [pr,pairW_avg,num,Fintype.card_fin] using
    gram_embedded_upper (pack _) (pack _) (pack_inj _) (pack_inj _) G
    (by simpa only [num,Fintype.card_fin] using hroom)

omit [DecidableEq I] in
private theorem kernel_complement_dimension {E : Type} [Fintype E] [DecidableEq E]
    (A : Mat I E) (hA : Injective A.mulVec) :
    dim (LinearMap.ker Aᵀ.mulVecLin)+Fintype.card E=Fintype.card I := by
  have hh := Aᵀ.mulVecLin.finrank_range_add_finrank_ker
  change Aᵀ.rank+dim (LinearMap.ker Aᵀ.mulVecLin)=dim (Vec I) at hh
  rw [Matrix.rank_transpose,mrk_inj.mp hA,dim_vec] at hh
  omega

/-- A fixed pair of image kernels costs its full ambient codimension, while
only the surviving Gram table is normalized. -/
theorem gram_kernel_joint_upper {E T : Type}
    [Fintype E] [Fintype T] [DecidableEq E] [DecidableEq T]
    (A : Mat I E) (C : Mat J T)
    (hA : Injective A.mulVec) (hC : Injective C.mulVec) (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    pr (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun z=>z.1*A=0 ∧ z.2*C=0 ∧ z.1ᵀ*z.2=G)≤
      2*bp (-num U*(num E+num T)-(num I-num E)*(num J-num T)) := by
  have he := kernel_complement_dimension A hA
  have ht := kernel_complement_dimension C hC
  have he' : (dim (LinearMap.ker Aᵀ.mulVecLin):ℝ)=num I-num E := by
    have hh : (dim (LinearMap.ker Aᵀ.mulVecLin):ℝ)+num E=num I := by exact_mod_cast he
    linarith
  have ht' : (dim (LinearMap.ker Cᵀ.mulVecLin):ℝ)=num J-num T := by
    have hh : (dim (LinearMap.ker Cᵀ.mulVecLin):ℝ)+num T=num J := by exact_mod_cast ht
    linarith
  have hroom' : (dim (LinearMap.ker Aᵀ.mulVecLin):ℝ)+
      dim (LinearMap.ker Cᵀ.mulVecLin)-num U≤-1 := by
    rw [he',ht']
    have hnE : 0≤num E := Nat.cast_nonneg _
    have hnT : 0≤num T := Nat.cast_nonneg _
    linarith
  have hPA : pr unif (fun P : Mat U I=>P*A=0)=bp (-num U*num E) := pr_mult_mat hA 0
  have hQC : pr unif (fun Q : Mat U J=>Q*C=0)=bp (-num U*num T) := pr_mult_mat hC 0
  rw [pair_restore _ _ _ _ (hPA.trans_gt (bp_pos _)) (hQC.trans_gt (bp_pos _)),
    on_unif,on_unif,hPA,hQC]
  refine (mul_le_mul_of_nonneg_left (gram_fixed_kernels_upper A C G hroom')
    (mul_nonneg (bp_pos _).le (bp_pos _).le)).trans_eq ?_
  rw [he',ht']
  rw [←bp_add,mul_left_comm _ (2:ℝ),←bp_add]
  congr 2
  ring

/-- A uniform lower bound retaining both frame injectivity conditions. -/
theorem gram_injective_lower (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    bp (-num I*num J)/4≤
      pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (gramGood G) := by
  have hroom₀ : num I+num J≤num U := by linarith
  have hgram := (gram_norm (U:=U) G hroom₀).2
  have hhalf : bp (-1)= (1:ℝ)/2 := by rw [bp_neg,bp_one]; norm_num
  have h1 : bp (num I-num U)≤(1:ℝ)/2 := by
    rw [←hhalf]
    apply bp_le
    have hnJ : 0≤num J := Nat.cast_nonneg _
    linarith
  have h2 : bp (num I+num J-num U)≤(1:ℝ)/2 := by
    rw [←hhalf]
    exact bp_le hroom
  have hmul : (1:ℝ)/4≤(1-bp (num I-num U))*(1-bp (num I+num J-num U)) := by
    nlinarith [mul_nonneg (show 0≤(1:ℝ)/2-bp (num I-num U) by linarith)
      (show 0≤(1:ℝ)/2-bp (num I+num J-num U) by linarith)]
  apply le_trans _ hgram
  rw [mul_assoc]
  nlinarith [mul_le_mul_of_nonneg_left hmul (bp_pos (-num I*num J)).le]

/-- A uniform lower bound on the unrestricted Gram normalization. -/
theorem gram_unrestricted_lower (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    bp (-num I*num J)/4≤
      pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G) :=
  (gram_injective_lower G hroom).trans
    (pr_mono (pairW_law unif_law unif_law).nz (fun _ h=>h.1))

/-- Passing from the Gram law to injective frames costs at most eight. -/
theorem gram_conditioned_injective_mass (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    (1:ℝ)/8≤pr (onW (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun z=>z.1ᵀ*z.2=G)) (fun z=>Injective z.1.mulVec ∧ Injective z.2.mulVec) := by
  rw [pr_on]
  have hl := gram_injective_lower (U:=U) G hroom
  have hu := gram_unrestricted_upper (U:=U) G hroom
  have hp : 0<pr (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G) :=
    (div_pos (bp_pos _) (by norm_num)).trans_le (gram_unrestricted_lower G hroom)
  apply (le_div_iff₀ hp).mpr
  change _≤pr _ (gramGood G)
  linarith

/-- Specified image-kernel dimensions survive Gram conditioning with the
ambient exponential penalty intact. -/
theorem gram_conditioned_kernel_bound {E T : Type}
    [Fintype E] [Fintype T] [DecidableEq E] [DecidableEq T]
    (A : Mat I E) (C : Mat J T)
    (hA : Injective A.mulVec) (hC : Injective C.mulVec) (G : Mat I J)
    (hroom : num I+num J-num U≤-1) :
    pr (onW (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun z=>z.1ᵀ*z.2=G)) (fun z=>z.1*A=0 ∧ z.2*C=0)≤
      8*bp ((num E+num T)*(num I+num J-num U)) := by
  rw [pr_on]
  let W : Wgt (Mat U I×Mat U J) := pairW unif unif
  have hn : pr W (fun z=>z.1ᵀ*z.2=G ∧ z.1*A=0 ∧ z.2*C=0)=
      pr W (fun z=>z.1*A=0 ∧ z.2*C=0 ∧ z.1ᵀ*z.2=G) := by
    congr 1
    ext z
    tauto
  rw [hn]
  have hp : 0<bp (-num I*num J)/4 := div_pos (bp_pos _) (by norm_num)
  refine (div_le_div₀ (mul_nonneg (by norm_num) (bp_pos _).le)
    (gram_kernel_joint_upper A C hA hC G hroom) hp
    (gram_unrestricted_lower G hroom)).trans ?_
  have hrew : (2*bp (-num U*(num E+num T)-(num I-num E)*(num J-num T)))/
      (bp (-num I*num J)/4)=
      8*bp (-num U*(num E+num T)-(num I-num E)*(num J-num T)+num I*num J) := by
    calc
      _=8*(bp (-num U*(num E+num T)-(num I-num E)*(num J-num T))/
          bp (-num I*num J)) := by ring
      _=_ := ?_
    rw [←bp_sub]
    congr 2
    ring
  rw [hrew]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply bp_le
  have hnI : 0≤num I := Nat.cast_nonneg _
  have hnJ : 0≤num J := Nat.cast_nonneg _
  have hnE : 0≤num E := Nat.cast_nonneg _
  have hnT : 0≤num T := Nat.cast_nonneg _
  nlinarith [mul_nonneg hnE hnI,mul_nonneg hnT hnJ,mul_nonneg hnE hnT]

omit [Fintype U] [DecidableEq I] [DecidableEq U] in
private theorem kernel_matrix_exists (P : Mat U I) (k : ℕ)
    (h : P.rank+k≤Fintype.card I) :
    ∃ A : Mat I (Fin k),Injective A.mulVec ∧ P*A=0 := by
  classical
  let S := LinearMap.ker P.mulVecLin
  have hx := P.mulVecLin.finrank_range_add_finrank_ker
  change P.rank+dim S=dim (Vec I) at hx
  rw [dim_vec] at hx
  have hle : k≤dim S := by omega
  obtain ⟨A,hA,h'⟩ := bounded_pack S k
  refine ⟨A,mrk_inj.mpr ?_,?_⟩
  · rw [←colSp_dim,h',min_eq_right hle,Fintype.card_fin]
  · apply coe_mv_inj
    change (P*A).mulVecLin=(0 : Mat U (Fin k)).mulVecLin
    rw [Matrix.mulVecLin_mul,Matrix.mulVecLin_zero]
    exact LinearMap.ext fun x=>hA (show A.mulVecLin x∈colSp A from ⟨x,rfl⟩)

/-- Uniform bounds for specified rank deficiencies under the Gram law.
The enumeration cost is linear in the number of nominal columns. -/
theorem gram_conditioned_deficiencies (G : Mat I J)
    (hroom : num I+num J-num U≤-1) (e f : ℕ) :
    pr (onW (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun z=>z.1ᵀ*z.2=G))
      (fun z=>z.1.rank+e≤Fintype.card I ∧ z.2.rank+f≤Fintype.card J)≤
      8*bp (((e:ℝ)+f)*(2*(num I+num J)-num U)) := by
  classical
  let W := onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G)
  have hW : ∀ z,0≤W z := normW_nonneg
    (subW_nonneg (pairW_law unif_law unif_law).nz _)
  let p (A : Mat I (Fin e)×Mat J (Fin f)) (z : Mat U I×Mat U J) :=
    Injective A.1.mulVec ∧ Injective A.2.mulVec ∧ z.1*A.1=0 ∧ z.2*A.2=0
  have hh (z : Mat U I×Mat U J)
      (hz : z.1.rank+e≤Fintype.card I ∧ z.2.rank+f≤Fintype.card J) : ∃ A,p A z := by
    obtain ⟨A,hA,hAz⟩ := kernel_matrix_exists z.1 e hz.1
    obtain ⟨C,hC,hCz⟩ := kernel_matrix_exists z.2 f hz.2
    exact ⟨(A,C),hA,hC,hAz,hCz⟩
  have hterm (A : Mat I (Fin e)×Mat J (Fin f)) : pr W (p A)≤
      8*bp (((e:ℝ)+f)*(num I+num J-num U)) := by
    by_cases hA : Injective A.1.mulVec
    · by_cases hC : Injective A.2.mulVec
      · simpa only [p,hA,hC,true_and,num,Fintype.card_fin] using
          gram_conditioned_kernel_bound A.1 A.2 hA hC G hroom
      · simp only [p,hC,and_false,false_and,pr_false]
        exact mul_nonneg (by norm_num) (bp_pos _).le
    · simp only [p,hA,false_and,pr_false]
      exact mul_nonneg (by norm_num) (bp_pos _).le
  refine ((pr_mono hW hh).trans (pr_exists_le hW p)).trans
    ((Finset.sum_le_sum (fun A _=>hterm A)).trans ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
  change (num (Mat I (Fin e))*num (Mat J (Fin f)))*_≤_
  rw [cast_mat,cast_mat]
  simp only [num,Fintype.card_fin] at *
  rw [←bp_add,mul_left_comm _ (8:ℝ),←bp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply bp_le
  have hnI : (0:ℝ)≤Fintype.card I := Nat.cast_nonneg _
  have hnJ : (0:ℝ)≤Fintype.card J := Nat.cast_nonneg _
  have hne : (0:ℝ)≤e := Nat.cast_nonneg _
  have hnf : (0:ℝ)≤f := Nat.cast_nonneg _
  nlinarith [mul_nonneg hnI hnf,mul_nonneg hnJ hne]

/-- An exponential tail for the total image-rank deficiency, after Gram
conditioning. This can be paid against an exponentially capped leaf law. -/
theorem gram_conditioned_kernel_tail (G : Mat I J)
    (hroom : num I+num J-num U≤-1) (d : ℕ) :
    pr (onW (pairW unif unif : Wgt (Mat U I×Mat U J))
      (fun z=>z.1ᵀ*z.2=G))
      (fun z=>d≤(Fintype.card I-z.1.rank)+(Fintype.card J-z.2.rank))≤
      8*(d+1)*bp ((d:ℝ)*(2*(num I+num J)-num U)) := by
  classical
  let W := onW (pairW unif unif : Wgt (Mat U I×Mat U J)) (fun z=>z.1ᵀ*z.2=G)
  have hW : ∀ z,0≤W z := normW_nonneg
    (subW_nonneg (pairW_law unif_law unif_law).nz _)
  let p (e : Fin (d+1)) (z : Mat U I×Mat U J) :=
    z.1.rank+e.val≤Fintype.card I ∧ z.2.rank+(d-e.val)≤Fintype.card J
  have hh (z : Mat U I×Mat U J)
      (hz : d≤(Fintype.card I-z.1.rank)+(Fintype.card J-z.2.rank)) : ∃ e,p e z := by
    let e : Fin (d+1) := ⟨min d (Fintype.card I-z.1.rank),
      Nat.lt_succ_of_le (min_le_left _ _)⟩
    refine ⟨e,?_⟩
    have hI := z.1.rank_le_card_width
    have hJ := z.2.rank_le_card_width
    dsimp only [p,e]
    omega
  have hterm (e : Fin (d+1)) : pr W (p e)≤
      8*bp ((d:ℝ)*(2*(num I+num J)-num U)) := by
    have he : (e.val:ℝ)+(d-e.val:ℕ)=d := by
      exact_mod_cast Nat.add_sub_of_le (Nat.le_of_lt_succ e.isLt)
    simpa only [he] using gram_conditioned_deficiencies G hroom e.val (d-e.val)
  refine ((pr_mono hW hh).trans (pr_exists_le hW p)).trans
    ((Finset.sum_le_sum (fun e _=>hterm e)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one]
  ring

end
end Lax793645Proofs.Simplifications
