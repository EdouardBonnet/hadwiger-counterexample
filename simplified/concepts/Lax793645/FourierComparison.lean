import Lax793645.ConstructionData

/-!
---
title: Fourier comparison for a conditional frame law
type: theorem
---
A bounded test on the Gram key space whose linear Fourier coefficients are
sufficiently small has small correlation with each permitted nominal phase and bounded
Fourier weight under a capped leaf law. The weight may be selected after observing the
orientation.
-/

namespace Lax793645.FourierComparison

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Filter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

axiom one_direct_capped_leaf_fourier (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤ M) (c b ε : ℝ) (hb : 0≤ b) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (mixer : Mixer p n),Fintype.card (Row p n)+2* p.h+3≤ M* n→
      ∀ (q : I→ F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M* n)))
        (ψ : Wgt (Inputs p n I)) (π : Wgt (OneUnit p n (M* n))),
      (∀ o,0≤π o)→(∀ o,π o≤ bp (c*(M* n:ℕ))* oneUnitRaw mixer (M* n) o)→
      (∀ x,|D x|≤1)→(∀ x,D x≠0 → oneOwnPart v.t q x)→
      (∀ ξ,|linearFourier D ξ|≤δ)→(∀ x,|ψ x|≤1)→
      pr π (oneQueryWeightBad v D ψ b ε)≤ bp (-(n:ℝ))

end

end Lax793645.FourierComparison
