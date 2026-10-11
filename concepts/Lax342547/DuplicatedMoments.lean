import Lax342547.NoCoverMoments

/-!
---
title: Moments across endpoint channel groups
type: definition and theorem
---
Copying the same original tensor across endpoint channels multiplies the character rank exponent without changing its original cover space.
-/

namespace Lax342547.DuplicatedMoments

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.ChannelCharacters Lax342547.TensorCharacters Lax342547.ComponentSpaces
open Lax342547.ComponentDuals Lax342547.CoverProjection
open scoped BigOperators

axiom duplicated_total_rank {e d I J : Type} [Fintype e] [Fintype d] [Fintype I] [Fintype J]
    (A : e → Matrix I J Binary) :
    (∑ i : e × d, (A i.1).rank) = Fintype.card d*∑ i : e, (A i).rank

axiom duplicated_even_moment_bound {e d I J Ω : Type}
    [Fintype e] [Fintype d] [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq e] [DecidableEq d] [DecidableEq I] [DecidableEq J]
    (μ : Ω → ℝ) (A : Ω → e → Matrix I J Binary) (ψ : Ω → ℝ) (h t : ℕ)
    (hμ : ∀ x, 0 ≤ μ x) (hψ : ∀ x, |ψ x| ≤ 1) :
    (∑ c, productLaw (fun _ : (e × d) × Fin h => channelLaw) c*
      |∑ x, μ x*ψ x*tensorCharacter h (fun i : e × d => A x i.1) c|^(2*t)) ≤
      ∑ sample : Fin (2*t) → Ω, productLaw (fun _ : Fin (2*t) => μ) sample/
        (2 : ℝ)^((Fintype.card d*h)*∑ a : e, (∑ i, A (sample i) a).rank)

end Lax342547.DuplicatedMoments
