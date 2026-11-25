import Lax793645Proofs.Simplifications.OnePhaseCoefficients
import Lax793645Proofs.Simplifications.SymmetricPhaseEnergy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneHeat (x : OneUnit p n N) (S : Party) : Ambient p (2*N):=
  fun e=>∑ i,S i • ((onePhaseCube (x i) e).2*(onePhaseCube (x i) e).1ᵀ)

def oneThermal {t : Comp p.g→ℕ} (x : OneUnit p n N) (S : Party)
    (T : ImageTuple (Comp p.g) t (2*N)) : ImageTuple (Comp p.g) t (2*N):=
  fun e=>(oneHeat x S e+(oneHeat x S e)ᵀ)*T e

def oneSparks {t : Comp p.g→ℕ} (x : OneUnit p n N) (S : Party)
    (T : ImageTuple (Comp p.g) t (2*N)) (i : Bool) (e : Comp p.g) :
    Mat (HyperbolicIdx p.h) (Fin (t e)):=
  S i • Matrix.fromRows ((onePhaseCube (x i) e).1ᵀ*T e) ((onePhaseCube (x i) e).2ᵀ*T e)

def oneTupleGlimpse {t : Comp p.g→ℕ} (x : OneUnit p n N) (i : Bool)
    (T : ImageTuple (Comp p.g) t (2*N)) : Prop:=
  ∀ e,Function.Injective ((onePhaseCube (x i) e).1ᵀ*T e).mulVec

/-- The polar action is an image of channel-only nominal vectors.
This is what permits joint counting with arbitrary primal companions. -/
theorem one_fused_thermal {t : Comp p.g→ℕ} (x : OneUnit p n N) (S : Party)
    (T : ImageTuple (Comp p.g) t (2*N)) (e : Comp p.g) :
    oneDualImages x e*oneChannelCoefficient (n:=n) (fun i=>oneSparks x S T i e)=
      oneThermal x S T e := by
  rw [one_fused_dual_images]
  simp only [oneSparks,Matrix.mul_smul,Matrix.fromCols_mul_fromRows,oneThermal,oneHeat,
    Matrix.transpose_sum,Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.add_mul,Matrix.sum_mul,Matrix.smul_mul,Matrix.mul_assoc,smul_add,
    Finset.sum_add_distrib]

theorem one_hot_channel_coefficient {t : Comp p.g→ℕ} (x : OneUnit p n N) (S : Party)
    (T : ImageTuple (Comp p.g) t (2*N)) (i : Bool) (hi : S i=1)
    (hT : oneTupleGlimpse x i T) (e : Comp p.g) :
    Function.Injective (oneChannelCoefficient (n:=n) (fun i=>oneSparks x S T i e)).mulVec := by
  apply one_channel_coefficient_inj _ i
  unfold oneSparks
  rw [hi,one_smul]
  intro u v h
  apply hT e
  have he:=congrArg (fun w : Vec (HyperbolicIdx p.h)=>fun j=>w (Sum.inl j)) h
  simpa only [Matrix.fromRows_mulVec,Sum.elim_inl] using he

theorem one_tone_heat (x : OneUnit p n N) (S : Party) (Δ : Ambient p (2*N)) :
    joinPhase p (oneListens x) S Δ=∑ e,mpair (oneHeat x S e) (Δ e) := by
  simp only [joinPhase,uPhase,oneHeat,mpair_sum,mpair_smul,LinearMap.sum_apply,
    LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro e _
  cases e <;> rfl

theorem one_tone_symmetric_offset {r : ℕ} {C : SymCover p (2*N)}
    (x : OneUnit p n N) (S : Party) (X : SymAtlas p r C) (Z : SymBatch X (2*N)) :
    joinPhase p (oneListens x) S (symSpelled X Z)=
      imageTuplePair (symBreadth X) (2*N) Z (oneThermal x S (symSrc X))+
      joinPhase p (oneListens x) S (symEdgeCost X) := by
  rw [one_tone_heat,one_tone_heat,symmetric_offset_phase]
  rfl

end
end Lax793645Proofs.Simplifications
