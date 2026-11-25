import Lax793645Proofs.Simplifications.LinearCellBounds
import Lax793645Proofs.Simplifications.CommonLinearFrequencies
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J K T : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype T] [DecidableEq T]

def frequencySpace (P : Mat J I) : Space (Vec I):=LinearMap.range Pᵀ.mulVecLin

theorem linear_fourier_pullback (P : Mat J I) (φ : Wgt (Vec J)) (ξ : Vec I) :
    linearFourier (fun x=>φ (P*ᵥx)) ξ=
      ∑ a : Vec J,linearFourier φ a*ind (ξ=Pᵀ*ᵥa) := by
  have he x : φ (P*ᵥx)=∑ a : Vec J,linearFourier φ a*vectorPhase (Pᵀ*ᵥa) x := by
    rw [←hat_eqn φ (P*ᵥx)]
    apply Finset.sum_congr rfl
    intro a _
    unfold linearFourier vectorPhase
    rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]
  change avg unif (fun x=>vectorPhase ξ x*φ (P*ᵥx))=_
  simp_rw [he,Finset.mul_sum,avg_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [←linear_fourier_character]
  unfold linearFourier
  rw [←avg_mul']
  apply avg_congr
  intro x _
  ring

theorem linear_partition_fourier_support (P : Mat J I) (φ : Wgt (Vec J))
    (ξ : Vec I) (hξ : ξ∉frequencySpace P) :
    linearFourier (fun x=>φ (P*ᵥx)) ξ=0 := by
  rw [linear_fourier_pullback]
  apply Finset.sum_eq_zero
  intro a _
  have ha : ξ≠Pᵀ*ᵥa:=fun he=>hξ ⟨a,he.symm⟩
  rw [ind_zero ha,mul_zero]

theorem linear_projection_fourier (P : Mat J I) (f : Wgt (Vec I)) (ξ : Vec I) :
    linearFourier (banner unif P.mulVec f) ξ=
      if ξ∈frequencySpace P then linearFourier f ξ else 0 := by
  split
  · rename_i hξ
    obtain ⟨a,ha⟩:=hξ
    have hc : vectorPhase ξ=(vectorPhase a)∘P.mulVec := by
      funext x
      rw [←ha]
      unfold vectorPhase
      change wsign ((Pᵀ*ᵥa)⬝ᵥx)=wsign (a⬝ᵥ(P*ᵥx))
      rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]
    have he:=cash_orth unif unif_law.nz P.mulVec f (vectorPhase a)
    rw [←hc] at he
    simpa only [linearFourier,dip,mul_comm] using he
  · rename_i hξ
    exact linear_partition_fourier_support P (cashbook unif P.mulVec f) ξ hξ

/-- Uniform linear partitions are conditionally independent over the
intersection of their frequency spaces. -/
theorem linear_uniform_common_overlap (P : Mat J I) (Q : Mat K I) (C : Mat T I)
    (hC : frequencySpace P⊓frequencySpace Q≤frequencySpace C)
    (φ : Wgt (Vec J)) (ψ : Wgt (Vec K)) :
    dip unif (fun x=>φ (P*ᵥx)) (fun x=>ψ (Q*ᵥx))=
      dip unif (banner unif C.mulVec (fun x=>φ (P*ᵥx)))
        (banner unif C.mulVec (fun x=>ψ (Q*ᵥx))) := by
  unfold dip
  rw [linear_fourier_pair,linear_fourier_pair]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [linear_projection_fourier,linear_projection_fourier]
  by_cases hc : ξ∈frequencySpace C
  · simp only [if_pos hc]
  · simp only [if_neg hc,mul_zero]
    have hn : ξ∉frequencySpace P ∨ ξ∉frequencySpace Q := by
      by_contra! hh
      exact hc (hC hh)
    rcases hn with hp|hq
    · rw [linear_partition_fourier_support P φ ξ hp,zero_mul]
    · rw [linear_partition_fourier_support Q ψ ξ hq,mul_zero]

end
end Lax793645Proofs.Simplifications
