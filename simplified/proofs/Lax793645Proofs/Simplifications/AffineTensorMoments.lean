import Lax793645Proofs.Simplifications.TensorIsolation
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MomentCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
noncomputable section

variable {S T : Type} [Fintype S] [Fintype T]

def tensorRay (s : Vec S) (t : Vec T) : Vec (S × T) := fun x => s x.1*t x.2

def affineTensorSpace (εS : Vec S) (εT : Vec T) : Space (Mat (S × T) (S × T)) :=
  Submodule.span F {w | ∃ s t, dotProduct εS s=1 ∧ dotProduct εT t=1 ∧
    w=vecMulVec (tensorRay s t) (tensorRay s t)}

structure TensorIdentities (εS : Vec S) (εT : Vec T)
    (w : Mat (S × T) (S × T)) : Prop where
  selector_sym : ∀ a b i j, w (a,i) (b,j)=w (b,i) (a,j)
  base_sym : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i)
  selector_diag : ∀ a i j, w (a,i) (a,j)=∑ b, εS b*w (a,i) (b,j)
  base_diag : ∀ a b i, w (a,i) (b,i)=∑ j, εT j*w (a,i) (b,j)

theorem tensorPoint_identities (s : Vec S) (t : Vec T) (εS : Vec S) (εT : Vec T)
    (hs : dotProduct εS s=1) (ht : dotProduct εT t=1) :
    TensorIdentities εS εT (vecMulVec (tensorRay s t) (tensorRay s t)) := by
  constructor
  · intro a b i j; dsimp [vecMulVec,tensorRay]; ring
  · intro a b i j; dsimp [vecMulVec,tensorRay]; ring
  · intro a i j
    change (s a*t i)*(s a*t j)=∑ b, εS b*((s a*t i)*(s b*t j))
    calc
      _ = (s a*s a)*(t i*t j) := by ring
      _ = s a*(t i*t j) := by rw [bit_sq]
      _ = (∑ b, εS b*s b)*(s a*(t i*t j)) := by rw [show (∑ b,εS b*s b)=1 from hs,one_mul]
      _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro b _; ring
  · intro a b i
    change (s a*t i)*(s b*t i)=∑ j, εT j*((s a*t i)*(s b*t j))
    calc
      _ = (s a*s b)*(t i*t i) := by ring
      _ = (s a*s b)*t i := by rw [bit_sq]
      _ = (∑ j, εT j*t j)*((s a*s b)*t i) := by rw [show (∑ j,εT j*t j)=1 from ht,one_mul]
      _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring

theorem affineTensor_identities (εS : Vec S) (εT : Vec T)
    {w : Mat (S × T) (S × T)} (hw : w ∈ affineTensorSpace εS εT) :
    TensorIdentities εS εT w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨s,t,hs,ht,rfl⟩ := hw
      exact tensorPoint_identities s t εS εT hs ht
  | zero => constructor <;> intros <;> simp
  | add w z _ _ hw hz =>
      constructor
      · intro a b i j; simp only [Matrix.add_apply,hw.selector_sym,hz.selector_sym]
      · intro a b i j; simp only [Matrix.add_apply,hw.base_sym,hz.base_sym]
      · intro a i j; simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib,
          hw.selector_diag,hz.selector_diag]
      · intro a b i; simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib,
          hw.base_diag,hz.base_diag]
  | smul c w _ hw =>
      constructor
      · intro a b i j; simp only [Matrix.smul_apply,hw.selector_sym]
      · intro a b i j; simp only [Matrix.smul_apply,hw.base_sym]
      · intro a i j
        simp only [Matrix.smul_apply,smul_eq_mul,hw.selector_diag,Finset.mul_sum,mul_left_comm]
      · intro a b i
        simp only [Matrix.smul_apply,smul_eq_mul,hw.base_diag,Finset.mul_sum,mul_left_comm]

/-- Every existing Boolean-feature moment belongs to the elementary affine
tensor space. This statement holds at every selector degree. -/
theorem Wspace_le_affineTensorSpace (p : Shape) (n : ℕ) :
    Wspace p n ≤ affineTensorSpace (Pi.single emptySel 1) (Pi.single none 1) := by
  classical
  apply Submodule.span_le.mpr
  rintro w ⟨s,z,rfl⟩
  apply Submodule.subset_span
  refine ⟨selV p.j s,baseV z,?_,?_,rfl⟩
  · simp [single_dotProduct,selV,emptySel]
  · simp [single_dotProduct,baseV]

theorem Wspace_tensor_identities (p : Shape) (n : ℕ) {w : Moment p n}
    (hw : w ∈ Wspace p n) :
    TensorIdentities (Pi.single emptySel 1) (Pi.single none 1) w :=
  affineTensor_identities _ _ (Wspace_le_affineTensorSpace p n hw)

end
end Lax793645Proofs.Simplifications
