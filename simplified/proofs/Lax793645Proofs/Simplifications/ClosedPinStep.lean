import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ImagePartitions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section

/-- Closing a violating pin event under `c` coordinate projections retains
the exponent with ζ replaced by ζ/c. The completion count is paid before
normalizing the retained law. -/
theorem closed_pin_step {A B : Type} [Fintype A] [Fintype B]
    (w : Wgt A) (hw : ∀ x,0≤w x) (E : A→Prop) (f : A→B)
    (N t u : ℕ) (c ζ : ℝ) (hc : 0<c) (hz : 0≤ζ) (htu : t≤u)
    (hu : (u:ℝ)≤c*t) (hb : num B≤bp (((u-t:ℕ):ℝ)*N))
    (he : fee N ζ t<pr w E) :
    ∃ y,fee N (ζ/c) u<pr w (fun x => E x ∧ f x=y) := by
  classical
  by_contra! h
  have hsum : pr w E≤∑ y:B,pr w (fun x => E x ∧ f x=y) :=
    (pr_mono hw (fun x hx => ⟨f x,hx,rfl⟩)).trans (pr_exists_le hw _)
  have hn : pr w E≤num B*fee N (ζ/c) u := hsum.trans
    ((Finset.sum_le_sum (fun y _ => h y)).trans_eq (by simp [num]))
  have hu' : (u:ℝ)/c≤t := (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hu)
  have hlast : num B*fee N (ζ/c) u≤fee N ζ t := by
    apply (mul_le_mul_of_nonneg_right hb (bp_pos _).le).trans
    unfold fee
    rw [←bp_add]
    apply bp_le
    have ht : ((u-t:ℕ):ℝ)=(u:ℝ)-t := Nat.cast_sub htu
    rw [ht]
    have hz' := mul_le_mul_of_nonneg_left hu' hz
    have heq : ζ*((u:ℝ)/c)=(ζ/c)*u := by ring
    rw [heq] at hz'
    nlinarith [mul_le_mul_of_nonneg_right hz' (show 0≤(N:ℝ) by positivity)]
  exact not_lt_of_ge (hn.trans hlast) he
end
end Lax793645Proofs.Simplifications
