import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteConditioning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section

variable {A B : Type} [Fintype A] [Fintype B]

/-- A coordinate that was sampled independently keeps a bounded marginal
when each allowed first coordinate accepts at least a fixed proportion
of its possible completions. -/
theorem free_coordinate_conditioning (w : Wgt A) (v : Wgt B)
    (hw : ∀ x,0≤w x) (hv : ∀ y,0≤v y) (P : A→Prop) (Q : A→B→Prop)
    {c : ℝ} (hc : 0<c) (hQ : ∀ x,P x→c≤pr v (Q x)) (y : B) :
    mapW (onW (pairW w v) (fun xy=>P xy.1 ∧ Q xy.1 xy.2)) Prod.snd y≤c⁻¹*v y := by
  classical
  let E:=fun xy : A×B=>P xy.1 ∧ Q xy.1 xy.2
  let z:=pr (pairW w v) E
  have hnn : ∀ xy,0≤pairW w v xy:=fun xy=>mul_nonneg (hw _) (hv _)
  have hden : c*pr w P≤z := by
    change c*avg w (fun x=>ind (P x))≤avg (pairW w v) (fun xy=>ind (P xy.1 ∧ Q xy.1 xy.2))
    rw [←avg_mul',pairW_avg]
    apply avg_mono hw
    intro x
    simp only [ind_and,avg_mul']
    by_cases hp : P x
    · simpa [hp,ind,pr] using hQ x hp
    · simp [hp,ind]
  rw [mapW,pr_on]
  change pr (pairW w v) (fun xy=>E xy ∧ xy.2=y)/z≤_
  by_cases hz : z=0
  · rw [hz,div_zero]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (hv y)
  have hz' : 0<z:=lt_of_le_of_ne (pr_nonneg hnn) (Ne.symm hz)
  apply (div_le_iff₀ hz').mpr
  have hnum : pr (pairW w v) (fun xy=>E xy ∧ xy.2=y)≤pr w P*v y := by
    apply (pr_mono hnn (fun xy h=>⟨h.1.1,h.2⟩) :
      pr (pairW w v) (fun xy=>E xy ∧ xy.2=y)≤
        pr (pairW w v) (fun xy=>P xy.1 ∧ xy.2=y)).trans_eq
    rw [pairW_pr w v P (fun z=>z=y),pr_point']
  apply hnum.trans
  have hh:=mul_le_mul_of_nonneg_left hden (mul_nonneg (inv_nonneg.mpr hc.le) (hv y))
  calc
    pr w P*v y=(c⁻¹*v y)*(c*pr w P) := by field_simp
    _≤_:=hh

end
end Lax793645Proofs.Simplifications
