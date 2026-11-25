import Lax793645.ConstructionData

/-!
---
title: From a conflict probability to a sampled graph
type: lemma
---
Assume the conflict lower bound for every admissible edge law of a finite
triangle-free hole relation. Sampling enough vertices gives a graph with independence
number at most 2 and connected matching number less than $m/100$ for a graph of order
$m$. The construction uses scale 2 in the general sampling estimate.
-/

namespace Lax793645.MatchingExposure

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open HadwigerMatching Real Filter

axiom transfer_scales {g : ℕ} (hg : 0 < g) {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Type) [Fintype A] [Nonempty A]
      (H : Holes A) (μ : Wgt A), IsLaw μ →
      (Fintype.card (A × A) : ℝ) ≤ bp (B * (N:ℝ)^2) →
      (∀ w : Wgt (A × A), IsLaw w → pairCaps μ (bp 1000) (bp (4000* g* N)) w →
        carried w H.unit → bp (-100* g* N) ≤ pr (pairW w w) (fun x => H.conflict x.1 x.2)) →
      ∃ x : Fin (ord g N) → A,
        (H.graph x).indepNum ≤ 2 ∧
        (connectedMatchingNumber (H.graph x) : ℚ) < (ord g N : ℚ)/100

end

end Lax793645.MatchingExposure
