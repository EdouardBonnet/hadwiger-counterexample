import Lax793645.ConstructionData

/-!
---
title: One partition for all filters on a leaf
type: lemma
---
For every fixed accuracy, a partition defined by a bounded number of linear equations
approximates every permitted filtered query density in mean absolute error. Its
projected densities have a bound independent of the accuracy.
-/

namespace Lax793645.FilteredQueryPartition

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Finset Matrix Function Filter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
axiom one_query_all_filters_linear_partition
    {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {p : Shape} (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤ M) (c L ε : ℝ) (hL : 0< L) (hε : 0<ε) :
    ∃ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2* p.h+3≤ M* n →
      ∀ (π : Wgt (OneUnit p n (M* n))),IsLaw π →
      (∀ o,π o≤ bp (c*(M* n:ℕ))* oneUnitRaw m (M* n) o) →
      ∀ (w : I→ Wgt (Knobs p.g n)),(∀ i,IsLaw (w i)) →
      (∀ i,mapW (w i) (freePart p)=unif) →
      (∀ x,prodW w x≤ L* unif x) → ∀ (q : I→ F) (χ : Inputs p n I→ A),
      let K:=oneQueryReferenceSet v q (M* n); let ν:=unifOn K
      let μ:=colored π (prodW w) (oneQueryFlags v χ)
      let d:=coloredCutDensities ν (prodW w) (oneQueryFlags v χ) (oneTemplateCoordinates v) K
      ∃ r : ℕ,r≤ R ∧ ∃ P : Mat (Fin r) (Fin (M* n)×Bool×KeySlots p v.t),
        ∀ t : Wgt (OneUnit p n (M* n)×(A×(I→ F))),
        (∀ i,0≤ t i) → (∀ i,t i≤μ i) →
        lcost ν (mixW t d) (banner ν P.mulVec (mixW t d))≤ε

end

end Lax793645.FilteredQueryPartition
