import Lax793645Proofs.Simplifications.AffineOptionContracts
import Lax793645Proofs.Simplifications.FiniteRejectionTransfer

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix Finset Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N : ℕ} {I A : Type} [Fintype I] [Fintype A]

theorem hist_total (v : A → Volley p n I) (t : Tagging p I)
    (μ : Wgt (UnitType p n N)) (rho : Wgt A) (U : A → UnitType p n N → Prop) :
    tot (Volley.hist v t μ rho U)=avg rho (fun a => pr μ (U a)) := by
  unfold tot Volley.hist
  rw [←avg_sum]
  simp_rw [sum_pr_tag]

/-- Rejecting a set of raw query inputs loses at most its original mass in
the entire key histogram, even with arbitrary orientation acceptance. -/
theorem hist_rejection (v : A → Volley p n I) (t : Tagging p I)
    (μ : Wgt (UnitType p n N)) (rho : Wgt A) (U : A → UnitType p n N → Prop)
    (G : A → Prop) (δ : ℝ) (hμ : SubLaw μ) (hrho : ∀ a,0 ≤ rho a)
    (hG : pr rho (fun a => ¬G a) ≤ δ) :
    let x := Volley.hist v t μ rho U
    let xg := Volley.hist v t μ rho (fun a o => G a ∧ U a o)
    (∀ k,0 ≤ xg k ∧ xg k ≤ x k) ∧ varOne x xg ≤ δ := by
  intro x xg
  have hdom k : xg k ≤ x k :=
    avg_mono hrho (fun a => pr_mono hμ.nz (fun o h => ⟨h.1.2,h.2⟩))
  refine ⟨fun k => ⟨avg_nonneg hrho (fun a => pr_nonneg hμ.nz),hdom k⟩,?_⟩
  have hvar : varOne x xg=tot x-tot xg := by
    unfold varOne tot
    simp_rw [abs_of_nonneg (sub_nonneg.mpr (hdom _))]
    rw [Finset.sum_sub_distrib]
  rw [hvar,hist_total,hist_total,←avg_sub]
  apply (avg_mono hrho (fun a => ?_)).trans hG
  by_cases ha : G a
  · simp [ha]
  simpa [ha] using ((pr_le_tot hμ.nz : pr μ (U a) ≤ tot μ).trans hμ.total)

theorem rejection_hit_lower {X : Type} [Fintype X] (rho : Wgt X)
    (U G : X → Prop) (δ : ℝ) (hrho : ∀ x,0 ≤ rho x)
    (hG : pr rho (fun x => ¬G x) ≤ δ) :
    pr rho U-δ ≤ pr rho (fun x => G x ∧ U x) := by
  have hh : pr rho U-pr rho (fun x => G x ∧ U x) ≤ pr rho (fun x => ¬G x) := by
    rw [pr,pr,←avg_sub]
    apply avg_mono hrho
    intro x
    by_cases h : G x
    · simp [h]
    simpa [h] using ind_le_one (U x)
  linarith

variable {q : Format} {d : Rates} {side : Bool}

theorem affine_sales_rejection (w : Quill p q d side)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (pin : Pin p n N) (K : ℕ) (μ : Wgt (UnitType p n N))
    (P : UnitType p n N → Prop) (m : Mixer p n) (s : Charts p n d)
    (hμ : SubLaw μ) (hm : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (hpen : affinePenSpace (w.pen t) pin.sp (affineQorth K) K) :
    (∀ k,0 ≤ AffineOptions.sales w t z pin K μ P m s k ∧
      AffineOptions.sales w t z pin K μ P m s k ≤ w.sales t z μ P m s k) ∧
    varOne (w.sales t z μ P m s) (AffineOptions.sales w t z pin K μ P m s) ≤
      bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) := by
  classical
  have hz i := dial_law p n _ _ _ hr hn (Quill.canDraw _ _ hm i)
  have h := hist_rejection (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o => P o ∧ w.deposit t z m o s x)
    (fun x => affineAvoids ((w.pen t).draw x) pin.sp (affineQorth K)) _
    hμ (prodW_law hz).nz (affine_query_rejection (w.pen t) pin.sp (affineQorth K) K hpen z hz)
  simpa only [Quill.sales,AffineOptions.sales,and_left_comm] using h

/-- Uniform in the orientation and the chosen key set, with no conditioning
on the compatible leaf-pair event. -/
theorem affine_sales_rejection_of_filter (w : Quill p q d side)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (pin : Pin p n N) (K : ℕ) (μ : Wgt (UnitType p n N))
    (P : UnitType p n N → Prop) (m : Mixer p n) (s : Charts p n d)
    (hμ : SubLaw μ) (hm : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (hpen : ∀ o,P o → affinePenSpace (w.pen t) pin.sp (affineQorth K) K) :
    (∀ k,0 ≤ AffineOptions.sales w t z pin K μ P m s k ∧
      AffineOptions.sales w t z pin K μ P m s k ≤ w.sales t z μ P m s k) ∧
    varOne (w.sales t z μ P m s) (AffineOptions.sales w t z pin K μ P m s) ≤
      bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) := by
  classical
  by_cases h : ∃ o,P o
  · obtain ⟨o,ho⟩ := h
    exact affine_sales_rejection w t z pin K μ P m s hμ hm hr hn (hpen o ho)
  have hP : ∀ o,¬P o := by simpa only [not_exists] using h
  simp [Quill.sales,AffineOptions.sales,Volley.hist,hP,pr_false,avg_zero,varOne,
    (bp_pos _).le]

/-- Uniform in the orientation and the chosen key set, with no conditioning
on the compatible leaf-pair event. -/
theorem affine_query_hit (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (pin : Pin p n N) (K : ℕ)
    (U : Inputs p n (Messenger q) → Prop)
    (hm : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (hpen : affinePenSpace (w.pen t) pin.sp (affineQorth K) K) :
    pr ((w.pen t).state z n) U-
      bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) ≤
    pr ((w.pen t).state z n)
      (fun x => affineAvoids ((w.pen t).draw x) pin.sp (affineQorth K) ∧ U x) := by
  have hz i := dial_law p n _ _ _ hr hn (Quill.canDraw _ _ hm i)
  exact rejection_hit_lower _ _ _ _ (prodW_law hz).nz
    (affine_query_rejection (w.pen t) pin.sp (affineQorth K) K hpen z hz)

end
end Lax793645Proofs.Simplifications
