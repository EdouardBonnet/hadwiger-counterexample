import Lax793645.OverlapTransfer
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates

import Lax793645Proofs.Simplifications.FiniteRejectionTransfer

namespace Lax793645Proofs.OverlapTransfer
open Lax793645.FiniteProbability Lax793645.OverlapTransfer

/--
---
conclusion: Lax793645.OverlapTransfer.finite_transfer
---
-/
theorem finite_transfer {A B : Type} [Fintype A] [Fintype B]
    (μ : Weight A) (hμ : Probability μ) (p : A → B) (R : ℝ) (hR : 0 ≤ R)
    (f g x y : Weight A) (hf : bounded f) (hg : bounded g)
    (hx : Subprobability x) (hy : Subprobability y)
    (hxs : dominatedSupport x μ) (hys : dominatedSupport y μ) :
    inner μ f g ^ 2 ≤ inner μ (density μ x) (density μ y) +
      |projectionError μ (clip R μ x) (clip R μ y) p| +
      ((cellError μ p f x + tail R μ x) + (cellError μ p g y + tail R μ y)) := by
  exact Upstream.OAI.HadwigerCounterexample.density_mend_implementation μ ⟨hμ.1, hμ.2⟩ p R hR
    f g x y hf hg ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxs hys

/--
---
conclusion: Lax793645.OverlapTransfer.clipped_transfer
---
-/
theorem clipped_transfer {A B : Type} [Fintype A] [Fintype B]
    (μ : Weight A) (hμ : Probability μ) (p : A → B) (R : ℝ) (hR : 0 ≤ R)
    (f g x y : Weight A) (hf : bounded f) (hg : bounded g)
    (hx : Subprobability x) (hy : Subprobability y)
    (hxs : dominatedSupport x μ) (hys : dominatedSupport y μ) :
    inner μ f g ^ 2 ≤ inner μ (clip R μ x) (clip R μ y) +
      |projectionError μ (clip R μ x) (clip R μ y) p| +
      ((cellError μ p f x + tail R μ x) + (cellError μ p g y + tail R μ y)) := by
  exact Simplifications.density_mend_clipped_implementation μ ⟨hμ.1, hμ.2⟩ p R hR
    f g x y hf hg ⟨hx.1, hx.2⟩ ⟨hy.1, hy.2⟩ hxs hys

end Lax793645Proofs.OverlapTransfer
