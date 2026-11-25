import Lax793645Proofs.Simplifications.ShiftMatrices
import Lax793645Proofs.Simplifications.ProtectedMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
variable {p : Shape} {n : ℕ}

def sharpMask (i : Row p n) : F := by
  classical
  exact if ∃ k, i.2 = some (Block.sharp,k) then 1 else 0

def sharpProjection (p : Shape) (n : ℕ) : Moment p n :=
  Matrix.diagonal sharpMask

def sharpConstant (p : Shape) (n : ℕ) : Mat (Row p n) (Fin n) :=
  embedMat (fun k => (emptySel, some (Block.sharp,k)))

/-- Replace exactly the sharp-by-sharp block, with the new matrix in the
constant-selector block and zero in all other selector blocks. -/
def sharpOverwrite (A : Moment p n) (B : Mat (Fin n) (Fin n)) : Moment p n :=
  A - sharpProjection p n*A*sharpProjection p n +
    sharpConstant p n*B*(sharpConstant p n).transpose

theorem sharpProjection_ray (s : Label p.b) :
    sharpProjection p n * blockRay p n s Block.sharp = blockRay p n s Block.sharp := by
  classical
  ext i j
  rw [sharpProjection, Matrix.diagonal_mul, blockRay_eval]
  by_cases he : i.2 = some (Block.sharp,j)
  · simp [sharpMask, he]
  · simp [he]

theorem sharpConstant_ray (s : Label p.b) :
    (sharpConstant p n).transpose * blockRay p n s Block.sharp = 1 := by
  classical
  rw [sharpConstant, embedMat_mul]
  ext i j
  simp [Matrix.submatrix, blockRay_eval, emptySel, monoBit, Matrix.one_apply, eq_comm]

theorem pull_sharpOverwrite (A : Moment p n) (B : Mat (Fin n) (Fin n))
    (s t : Label p.b) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (sharpOverwrite A B) = B := by
  let Q := blockRay p n s Block.sharp
  let R := blockRay p n t Block.sharp
  let D := sharpProjection p n
  let E := sharpConstant p n
  have hd : D.transpose=D := Matrix.diagonal_transpose _
  have hl : Q.transpose*D=Q.transpose := by
    have h := congrArg Matrix.transpose (sharpProjection_ray (n:=n) s)
    simpa [Q, D, Matrix.transpose_mul, sharpProjection] using h
  have hr : D*R=R := sharpProjection_ray t
  have he : Q.transpose*E=1 := by
    have h := congrArg Matrix.transpose (sharpConstant_ray (n:=n) s)
    simpa [Q, E, Matrix.transpose_mul] using h
  have hf : E.transpose*R=1 := sharpConstant_ray t
  have hD : pullM Q R (D*A*D) = pullM Q R A := by
    simp only [pullM_def]
    calc
      Q.transpose*(D*A*D)*R = (Q.transpose*D)*A*(D*R) := by simp [Matrix.mul_assoc]
      _ = Q.transpose*A*R := by rw [hl,hr]
  have hE : pullM Q R (E*B*E.transpose) = B := by
    simp only [pullM_def]
    calc
      Q.transpose*(E*B*E.transpose)*R = (Q.transpose*E)*B*(E.transpose*R) := by
        simp [Matrix.mul_assoc]
      _ = B := by rw [he,hf,Matrix.one_mul,Matrix.mul_one]
  change pullM Q R (A-D*A*D+E*B*E.transpose)=B
  rw [map_add,map_sub,hD,hE,sub_self,zero_add]

theorem sharpMask_Z (i : Row p n) (hi : isZRow i) : sharpMask i = 0 := by
  classical
  obtain ⟨k,hk⟩ := hi
  simp [sharpMask,hk,Block.Z,Block.sharp]

theorem sharpConstant_Z (i : Row p n) (hi : isZRow i) (j : Fin n) :
    sharpConstant p n i j = 0 := by
  classical
  obtain ⟨k,hk⟩ := hi
  have he : i ≠ (emptySel, some (Block.sharp,j)) := by
    intro h
    have := congrArg Prod.snd h
    simp [hk,Block.Z,Block.sharp] at this
  simp [sharpConstant,embedMat,he]

theorem sharpOverwrite_preserves_Z (A : Moment p n) (B : Mat (Fin n) (Fin n)) :
    agreesAt isZRow A (sharpOverwrite A B) := by
  classical
  intro i j hij
  simp only [sharpOverwrite,Matrix.add_apply,Matrix.sub_apply,
    sharpProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  rcases hij with hi | hj
  · rw [sharpMask_Z i hi,zero_mul,zero_mul,sub_zero]
    have he : (sharpConstant p n*B*(sharpConstant p n).transpose) i j=0 := by
      simp [Matrix.mul_apply,sharpConstant_Z i hi]
    rw [he,add_zero]
  · rw [sharpMask_Z j hj,mul_zero,sub_zero]
    have he : (sharpConstant p n*B*(sharpConstant p n).transpose) i j=0 := by
      simp [Matrix.mul_apply,Matrix.transpose_apply,sharpConstant_Z j hj]
    rw [he,add_zero]

def halfEmbedding (n : ℕ) : (Fin (n/2) ⊕ Fin (n/2)) ↪ Fin n where
  toFun := Sum.elim (fun i => ⟨i.val,by omega⟩) (fun i => ⟨n/2+i.val,by omega⟩)
  inj' := by
    intro i j h
    have he := congrArg Fin.val h
    cases i with
    | inl i => cases j with
      | inl j => congr; apply Fin.ext; exact he
      | inr j => simp only [Sum.elim_inl,Sum.elim_inr] at he; omega
    | inr i => cases j with
      | inl j => simp only [Sum.elim_inl,Sum.elim_inr] at he; omega
      | inr j => congr; apply Fin.ext; simp only [Sum.elim_inr] at he; omega

def embedHalf (n : ℕ) : Mat (Fin (n/2) ⊕ Fin (n/2)) (Fin (n/2) ⊕ Fin (n/2)) →ₗ[F]
    Mat (Fin n) (Fin n) := liftM (embedMat (halfEmbedding n)) (embedMat (halfEmbedding n))

theorem embedHalf_transpose (A : Mat (Fin (n/2) ⊕ Fin (n/2)) (Fin (n/2) ⊕ Fin (n/2))) :
    embedHalf n A.transpose = (embedHalf n A).transpose := by
  simp only [embedHalf,liftM_def,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem embedHalf_rank (A : Mat (Fin (n/2) ⊕ Fin (n/2)) (Fin (n/2) ⊕ Fin (n/2))) :
    A.rank ≤ (embedHalf n A).rank := by
  let E := embedMat (halfEmbedding n)
  have he : E.transpose*E=1 := embedMat_self (halfEmbedding n).injective
  have hm : E.transpose*embedHalf n A*E=A := by
    change E.transpose*(E*A*E.transpose)*E=A
    calc
      _ = (E.transpose*E)*A*(E.transpose*E) := by simp [Matrix.mul_assoc]
      _ = A := by rw [he,Matrix.one_mul,Matrix.mul_one]
  calc
    A.rank = (E.transpose*embedHalf n A*E).rank := congrArg Matrix.rank hm.symm
    _ ≤ (E.transpose*embedHalf n A).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (embedHalf n A).rank := Matrix.rank_mul_le_right _ _

def explicitShift (n k : ℕ) : Mat (Fin n) (Fin n) :=
  embedHalf n (Matrix.fromBlocks 0 (shiftedDiagonal (K:=F) (n/2) k) 0 0)

theorem explicitShift_parity {R : ℕ} (a b : Fin R → F) :
    (∑ k, a k • explicitShift n k.val) + (∑ k, b k • (explicitShift n k.val).transpose) =
    embedHalf n (Matrix.fromBlocks 0
      (∑ k, a k • shiftedDiagonal (K:=F) (n/2) k.val)
      (∑ k, b k • shiftedDiagonal (K:=F) (n/2) k.val).transpose 0) := by
  simp only [explicitShift,← embedHalf_transpose,← map_smul,← map_sum,← map_add]
  congr 1
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.sum_apply,Matrix.smul_apply,Matrix.transpose_apply,Matrix.fromBlocks]

theorem explicitShift_rank {R : ℕ} (a b : Fin R → F) (h : a ≠ 0 ∨ b ≠ 0) :
    n/2-(R-1) ≤ ((∑ k, a k • explicitShift n k.val) +
      (∑ k, b k • (explicitShift n k.val).transpose)).rank := by
  rw [explicitShift_parity]
  exact (bidirectional_diagonal_rank _ _ a b h).trans (embedHalf_rank _)

def mixerCount (p : Shape) := Fintype.card (MOne p)
def mixerIndex (p : Shape) : MOne p ≃ Fin (mixerCount p) := Fintype.equivFin _

def explicitMixer (m : Mixer p n) : Mixer p n where
  mixL j e f := sharpOverwrite (m.mixL j e f)
    (explicitShift n (mixerIndex p ((j,e,f),true)).val)
  mixR j e f := sharpOverwrite (m.mixR j e f)
    (explicitShift n (mixerIndex p ((j,e,f),false)).val)
  mixM ρ := explicitShift n (mixerCount p+ρ.val)

theorem explicitMixer_sameZ (m : Mixer p n) : sameZMixers m (explicitMixer m) := by
  constructor
  · intro j e f; exact sharpOverwrite_preserves_Z _ _
  · intro j e f; exact sharpOverwrite_preserves_Z _ _

theorem explicitMixer_unary (m : Mixer p n) (K s0 : ℕ) (h : unaryGood m K s0) :
    unaryGood (explicitMixer m) K s0 :=
  unaryGood_preserved m (explicitMixer m) (explicitMixer_sameZ m) K s0 h

theorem pull_ordered_explicit (m : Mixer p n) (s t : Label p.b) (i : MOne p) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (orderedM (explicitMixer m) i) = explicitShift n (mixerIndex p i).val := by
  rcases i with ⟨i,b⟩
  cases b <;> simp [orderedM,explicitMixer,pull_sharpOverwrite]

theorem pull_transpose_pair {I J K : Type} [Fintype I] (Q : Mat I J) (R : Mat I K)
    (A : Mat I I) : pullM Q R A.transpose = (pullM R Q A).transpose := by
  simp only [pullM_def,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]

theorem pull_either_explicit (m : Mixer p n) (s t : Label p.b) (i : MOne p) (b : Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (eitherM b (orderedM (explicitMixer m) i)) =
      eitherM b (explicitShift n (mixerIndex p i).val) := by
  cases b <;> simp [eitherM,pull_transpose_pair,pull_ordered_explicit]

theorem pull_self_explicit (m : Mixer p n) (s t : Label p.b) (hj : 1 ≤ p.j) (b : Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (eitherM b (selfM p n (explicitMixer m).mixM)) =
      eitherM b (∑ ρ, (s ρ+t ρ) • explicitShift n (mixerCount p+ρ.val)) := by
  cases b
  · simp only [eitherM, Bool.false_eq_true, if_false, pull_transpose_pair,
      pull_self_sharp _ _ _ hj, explicitMixer]
    simp_rw [add_comm (t _)]
  · simp [eitherM,pull_self_sharp _ _ _ hj,explicitMixer]

def parityCoefficients (p : Shape) (c : Vec (MBits p)) (b : Vec Bool)
    (s t : Label p.b) (v : Bool) : Fin (mixerCount p+p.b) → F :=
  mixerCoefficients (fun k => c ((mixerIndex p).symm k,v)) (b v) s t

theorem parityCoefficients_sum (c : Vec (MBits p)) (b : Vec Bool)
    (s t : Label p.b) (v : Bool) :
    (∑ k, parityCoefficients p c b s t v k • explicitShift n k.val) =
    (∑ i : MOne p, c (i,v) • explicitShift n (mixerIndex p i).val) +
      b v • (∑ ρ, (s ρ+t ρ) • explicitShift n (mixerCount p+ρ.val)) := by
  rw [Fin.sum_univ_add]
  simp only [parityCoefficients,mixerCoefficients,Fin.addCases_left,Fin.addCases_right,
    Fin.val_castAdd,Fin.val_natAdd,Finset.smul_sum,smul_smul]
  congr 1
  simpa only [Equiv.symm_apply_apply] using (Equiv.sum_comp (mixerIndex p) (fun k =>
    c ((mixerIndex p).symm k,v) • explicitShift n k.val)).symm

theorem pull_parity_explicit (m : Mixer p n) (s t : Label p.b) (hj : 1 ≤ p.j)
    (c : Vec (MBits p)) (b : Vec Bool) :
    pullM (blockRay p n s Block.sharp) (blockRay p n t Block.sharp)
      (indexedSum (explicitMixer m) c+selfSum (explicitMixer m) b) =
      (∑ k, parityCoefficients p c b s t true k • explicitShift n k.val) +
      (∑ k, parityCoefficients p c b s t false k • (explicitShift n k.val).transpose) := by
  simp only [indexedSum,selfSum,map_add,map_sum,map_smul,pull_either_explicit,
    pull_self_explicit m s t hj]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,eitherM,Bool.false_eq_true,if_false,if_true,
    Finset.sum_add_distrib]
  have ht := parityCoefficients_sum (n:=n) c b s t true
  have hf := congrArg Matrix.transpose (parityCoefficients_sum (n:=n) c b s t false)
  simp only [Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_add] at hf
  rw [ht,hf]
  simp only [Matrix.transpose_sum,Matrix.transpose_smul]
  exact add_add_add_comm (G:=Mat (Fin n) (Fin n)) _ _ _ _

theorem parityCoefficients_nonzero (c : Vec (MBits p)) (b : Vec Bool)
    (s t : Label p.b) (hst : s ≠ t) (h : c ≠ 0 ∨ b ≠ 0) :
    parityCoefficients p c b s t true ≠ 0 ∨ parityCoefficients p c b s t false ≠ 0 := by
  classical
  have hbase : (fun k => c ((mixerIndex p).symm k,true)) ≠ 0 ∨
      (fun k => c ((mixerIndex p).symm k,false)) ≠ 0 ∨ b true ≠ 0 ∨ b false ≠ 0 := by
    by_contra! hz
    rcases h with hc | hb
    · apply hc
      funext i
      rcases i with ⟨i,v⟩
      cases v
      · simpa using congr_fun hz.2.1 (mixerIndex p i)
      · simpa using congr_fun hz.1 (mixerIndex p i)
    · apply hb
      funext v
      cases v
      · exact hz.2.2.2
      · exact hz.2.2.1
  rcases hbase with h1 | h2 | h3 | h4
  · exact Or.inl (mixerCoefficients_nonzero _ _ s t hst (Or.inl h1))
  · exact Or.inr (mixerCoefficients_nonzero _ _ s t hst (Or.inl h2))
  · exact Or.inl (mixerCoefficients_nonzero _ _ s t hst (Or.inr h3))
  · exact Or.inr (mixerCoefficients_nonzero _ _ s t hst (Or.inr h4))

theorem explicitMixer_binary_rank (m : Mixer p n) (hj : 1 ≤ p.j)
    (hn : 4*(mixerCount p+p.b)+4 ≤ n) (s t : Label p.b) (hst : s ≠ t)
    (c : Vec (MBits p)) (b : Vec Bool) (h : c ≠ 0 ∨ b ≠ 0) :
    n ≤ 5*blockRank Block.sharp s t (indexedSum (explicitMixer m) c+selfSum (explicitMixer m) b) := by
  unfold blockRank
  rw [pull_parity_explicit m s t hj]
  have hr := explicitShift_rank (n:=n) _ _ (parityCoefficients_nonzero c b s t hst h)
  have hmargin := shift_rank_fifth hn
  omega

end
end Lax793645Proofs.Simplifications
