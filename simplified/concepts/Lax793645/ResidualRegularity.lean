import Lax793645.FiniteProbability

/-!
---
title: A common partition by energy increments
type: lemma
---
For a random finite family of functions bounded by $R$, one partition makes
the mean absolute residual correlation with every bounded test at most
$\varepsilon$. The number of cells depends only on $R$ and $\varepsilon$,
not on either finite space. Successive refinements by one sign bit prove this
using the energy $\mathbb E_i\|\Pi f_i\|_2^2\le R^2$.
-/

namespace Lax793645.ResidualRegularity
open FiniteProbability

axiom common_partition (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ bound : ℕ, ∀ (A I : Type) [Fintype A] [Fintype I]
      (α : Weight I) (μ : Weight A) (f : I → Weight A),
      Probability α → Probability μ → (∀ i x, |f i x| ≤ R) →
      ∃ k : ℕ, k ≤ bound ∧ ∃ p : A → Fin k,
        ∀ h : Weight A, (∀ x, |h x| ≤ 1) →
          expectation α (fun i => |inner μ (fun x => f i x - project μ p (f i) x) h|) ≤ ε

end Lax793645.ResidualRegularity
