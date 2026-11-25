import Lax793645Proofs.Simplifications.OneQueryCappedMoment

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def oneQueryWeightBad (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (b ε : ℝ) (o : OneUnit p n N) : Prop :=
  ∃ w : Wgt (Inputs p n I),inputFourierNorm w≤b ∧
    ε < |avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w x)|

theorem one_query_input_weight_moment (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ w : Wgt (Inputs p n I))
    (b : ℝ) (hb : 0≤b) (hw : inputFourierNorm w≤b) (o : OneUnit p n N) (ℓ : ℕ) :
    |avg unif (fun x=>D (oneTemplateCoordinates v o x)*ψ x*w x)|^(4*ℓ)≤
      b^(4*ℓ)*(oneQueryFourth v D ψ o)^ℓ := by
  have hh:=fourier_weight_moment
    (fun x=>D (oneTemplateCoordinates v o (inputCoordinates p n I x))*ψ (inputCoordinates p n I x))
    (fun x=>w (inputCoordinates p n I x)) b hb hw ℓ
  have he:=input_average (fun y=>D (oneTemplateCoordinates v o y)*ψ y*w y)
  have hq:=input_fourth (fun y=>D (oneTemplateCoordinates v o y)*ψ y)
  change |avg unif (fun x=>(fun y=>D (oneTemplateCoordinates v o y)*ψ y*w y)
    (inputCoordinates p n I x))|^(4*ℓ)≤b^(4*ℓ)*
    (additiveFourth (fun x=>(fun y=>D (oneTemplateCoordinates v o y)*ψ y)
      (inputCoordinates p n I x)))^ℓ at hh
  rw [he,hq] at hh
  exact hh

/-- Simultaneous control of every permitted input weight, including a
weight chosen after seeing the sampled orientation. -/
theorem one_query_uniform_weight_moment (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (μ π : Wgt (OneUnit p n N)) (b C ε : ℝ)
    (hπ : ∀ o,0≤π o) (hcap : ∀ o,π o≤C*μ o)
    (hb : 0≤b) (hε : 0≤ε) (ℓ : ℕ) :
    ε^(4*ℓ)*pr π (oneQueryWeightBad v D ψ b ε)≤
      C*b^(4*ℓ)*avg μ (fun o=>(oneQueryFourth v D ψ o)^ℓ) := by
  have hp o : ε^(4*ℓ)*ind (oneQueryWeightBad v D ψ b ε o)≤
      b^(4*ℓ)*(oneQueryFourth v D ψ o)^ℓ := by
    by_cases ho : oneQueryWeightBad v D ψ b ε o
    · rw [ind_one ho,mul_one]
      obtain ⟨w,hw,he⟩:=ho
      exact (pow_le_pow_left₀ hε he.le _).trans (one_query_input_weight_moment v D ψ w b hb hw o ℓ)
    · rw [ind_zero ho,mul_zero]
      exact mul_nonneg (pow_nonneg hb _) (pow_nonneg (one_query_fourth_nonneg v D ψ o) _)
  change ε^(4*ℓ)*avg π (fun o=>ind (oneQueryWeightBad v D ψ b ε o))≤_
  rw [←avg_mul']
  refine (avg_mono hπ hp).trans ?_
  unfold avg
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  have hh:=mul_le_mul_of_nonneg_right (hcap o)
    (mul_nonneg (pow_nonneg hb (4*ℓ)) (pow_nonneg (one_query_fourth_nonneg v D ψ o) ℓ))
  exact hh.trans_eq (by ring)

end
end Lax793645Proofs.Simplifications
