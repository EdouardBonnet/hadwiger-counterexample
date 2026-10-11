import Lax342547.NoCoverRank
import Lax342547.AdaptiveUnion
import Lax342547.CoverClasses
import Lax342547.FiniteSampling
import Lax342547.ListDeficits
import Lax342547.ModeBudgets
import Lax342547.NoCoverCertificate

namespace Lax342547Proofs.NoCoverRank
open Lax342547.NoCoverRank

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverProjection Lax342547.CoverClasses
open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.NoCoverRank.no_cover_rank_probability
---
-/
theorem no_cover_rank_probability {K V W ι Ω : Type} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (μ : Ω → ℝ) (M : Ω → V →ₗ[K] W) (P : Submodule K W → Prop)
    (Q : Submodule K (Module.Dual K V) → Prop) (r p : ℝ) (k n : ℕ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r)
    (hM : ∀ x, (Module.finrank K (LinearMap.range (M x)) : ℝ) ≤ r)
    (hP : JoinClosed P) (hQ : JoinClosed Q)
    (hPC : ∀ x, P (LinearMap.range (M x))) (hQR : ∀ x, Q (LinearMap.range (M x).dualMap))
    (hcard : Fintype.card ι = 2^k) (hnk : n ≤ k) (hn : 16*r < n)
    (hcover : ∀ S T, P S → Q T →
      (Module.finrank K S : ℝ) ≤ r*Fintype.card ι →
      (Module.finrank K T : ℝ) ≤ r*Fintype.card ι →
      cellMass μ (fun x => projection (M x) S T = 0) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => (Module.finrank K (LinearMap.range (∑ i, M (sample i))) : ℝ) < (2^(k-n) : ℝ)/4) ≤
      (4 : ℝ)^Fintype.card ι*p^(2^(k-n)) := by
  classical
  let A := fun E : Finset ι => fun exposed : E → Ω => fun x : Ω =>
    projection (M x) (Finset.univ.sup (fun i : E => LinearMap.range (M (exposed i))))
      (Finset.univ.sup (fun i : E => LinearMap.range (M (exposed i)).dualMap)) = 0
  have hA : ∀ E exposed, cellMass μ (A E exposed) ≤ p := by
    intro E exposed
    apply hcover
    · exact Lax342547.CoverClasses.finite_join_closed P hP _ _ (fun i _ => hPC _)
    · exact Lax342547.CoverClasses.finite_join_closed Q hQ _ _ (fun i _ => hQR _)
    · have hb := Lax342547.ModeBudgets.mode_span_budget
        (fun i : E => LinearMap.range (M (exposed i))) r hr (fun i => hM _) Finset.univ
      exact hb.trans (mul_le_mul_of_nonneg_left (by rw [Fintype.card_coe]; exact_mod_cast (Finset.card_le_univ E)) hr)
    · have hb := Lax342547.ModeBudgets.mode_span_budget
        (fun i : E => LinearMap.range (M (exposed i)).dualMap) r hr
        (fun i => by simpa only [LinearMap.finrank_range_dualMap_eq_finrank_range] using hM (exposed i)) Finset.univ
      exact hb.trans (mul_le_mul_of_nonneg_left (by rw [Fintype.card_coe]; exact_mod_cast (Finset.card_le_univ E)) hr)
  have hcert : ∀ sample : ι → Ω,
      (Module.finrank K (LinearMap.range (∑ i, M (sample i))) : ℝ) < (2^(k-n) : ℝ)/4 →
      ∃ E J : Finset ι, Disjoint E J ∧ 2^(k-n) ≤ J.card ∧
        ∀ j ∈ J, A E (fun e => sample e.val) (sample j) := by
    intro sample hs
    obtain ⟨E,J,hd,hk,hcov⟩ := Lax342547.NoCoverCertificate.low_rank_cover_certificate
      (fun i => M (sample i)) r k n (fun i => hM _) hcard hnk hn hs
    refine ⟨E,J,hd,hk,?_⟩
    intro j hj
    have hC := Lax342547.ListDeficits.finset_span_eq (fun i => LinearMap.range (M (sample i))) E
    have hR := Lax342547.ListDeficits.finset_span_eq (fun i => LinearMap.range (M (sample i)).dualMap) E
    have hC' : Finset.univ.sup (fun i : E => LinearMap.range (M (sample i.val))) = E.sup (fun i => LinearMap.range (M (sample i))) := by
      rw [Finset.sup_eq_iSup]
      simpa using hC
    have hR' : Finset.univ.sup (fun i : E => LinearMap.range (M (sample i.val)).dualMap) = E.sup (fun i => LinearMap.range (M (sample i)).dualMap) := by
      rw [Finset.sup_eq_iSup]
      simpa using hR
    dsimp only [A]
    rw [hC',hR']
    exact hcov j hj
  have hprob := Lax342547.FiniteSampling.product_probability (fun _ : ι => μ) (fun _ => hμ)
  exact (Lax342547.FiniteSampling.cell_mass_mono _ _ _ hprob.1 hcert).trans
    (Lax342547.AdaptiveUnion.adaptive_cover_union μ A p (2^(k-n)) hμ hp0 hp1 hA)

end Lax342547Proofs.NoCoverRank
