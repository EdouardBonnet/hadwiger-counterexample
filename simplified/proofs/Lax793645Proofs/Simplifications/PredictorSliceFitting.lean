import Lax793645Proofs.Simplifications.PolynomialFixedAccuracy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C Y : Type} [Fintype C] [Fintype Y]

/-- Fixing the tester and the remaining input variables gives a common
slice fit. The loss is the reciprocal tester mass, independent of the
number of common coordinates. -/
theorem predictor_slice_fit (μ : Wgt C) (ν : Wgt Y)
    (hμ : IsLaw μ) (hν : IsLaw ν) (φ : F→C→F) (q : Y→F)
    (R : C→Y→F) (b : F) (ε : ℝ)
    (hq : (1/4:ℝ)≤pr ν (fun y=>q y=b))
    (he : pr (pairW μ ν) (fun x=>φ (q x.2) x.1≠R x.1 x.2)≤ε) :
    ∃ y,q y=b ∧ pr μ (fun c=>φ b c≠R c y)≤4*ε := by
  classical
  let S := Finset.univ.filter (fun y=>q y=b)
  have hS : S.Nonempty := by
    by_contra hz
    have hh (y : Y) : q y≠b := by
      intro hy
      exact hz ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩⟩
    have hzero : pr ν (fun y=>q y=b)=0 := by
      simp only [pr,ind_zero (hh _),avg_zero]
    rw [hzero] at hq
    norm_num at hq
  let err (y : Y) := pr μ (fun c=>φ b c≠R c y)
  obtain ⟨y,hy,hmin⟩ := Finset.exists_min_image S err hS
  have hq_y : q y=b := (Finset.mem_filter.mp hy).2
  have hpoint (z : Y) : err y*ind (q z=b)≤
      pr μ (fun c=>φ (q z) c≠R c z) := by
    by_cases hz : q z=b
    · rw [ind_one hz,mul_one,hz]
      exact hmin z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩)
    · rw [ind_zero hz,mul_zero]
      exact pr_nonneg hμ.nz
  have havg := avg_mono hν.nz hpoint
  have htotal : err y*pr ν (fun z=>q z=b)≤ε := by
    have heq : avg ν (fun z=>pr μ (fun c=>φ (q z) c≠R c z))=
        pr (pairW μ ν) (fun x=>φ (q x.2) x.1≠R x.1 x.2) := by
      simp only [pr,pairW_avg]
      exact avg_avg _ _ _
    rw [avg_mul',heq] at havg
    exact havg.trans he
  have hn : 0≤err y := pr_nonneg hμ.nz
  refine ⟨y,hq_y,?_⟩
  nlinarith only [mul_le_mul_of_nonneg_left hq hn,htotal]

/-- Both fitted slices approximate the common predictor under any
independent tester law. No normalization of a key cell is involved. -/
theorem predictor_fit_transfer (μ : Wgt C) (ν : Wgt Y)
    (hμ : IsLaw μ) (hν : IsLaw ν) (φ : F→C→F) (q : Y→F)
    (Q : F→C→F) (ε : ℝ)
    (he : ∀ b,pr μ (fun c=>φ b c≠Q b c)≤ε) :
    pr (pairW μ ν) (fun x=>φ (q x.2) x.1≠Q (q x.2) x.1)≤ε := by
  unfold pr
  rw [pairW_avg,avg_avg]
  exact hν.avg_le (fun y=>he (q y))

end
end Lax793645Proofs.Simplifications
