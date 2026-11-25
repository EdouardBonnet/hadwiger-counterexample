import Lax793645.ConstructionData

/-!
---
title: Hits by a base query
type: lemma
---
For any fixed positive-mass set given by a bounded product test, the base query puts a
fixed fraction of its reference mass on the set outside an exponentially small
exceptional population. The fraction is independent of the number of product tests.
-/

namespace Lax793645.BaseQueryHits

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
open Lax793645.ConstructionData.Frames.OneQuill
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {K s0:ℕ}

axiom one_base_product_relative_hit (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→ F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤ M) (C:ℝ) (k:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ c:ℝ,0< c ∧ ∀ᶠ n:ℕ in atTop,let N:=M* n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)* n)) →
      (∀ x,u x≤ bp (C*(2* N))* oneUnitRaw m N x) →
      Fintype.card (Row p n)+2* p.h+3≤ N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ H:OneKeys t N→ Prop,OneDesign t (fun x=> ind (H x)) k →
      ε≤ pr (oneLawNu p N t z) H →
      pr u (fun o=>¬OneBaseSober w t z K H m
        (oneDilate w t K*(pr (oneLawNu p N t z) H/4)) o)≤ bp (-c* n)

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology BigOperators
open Lax793645.ConstructionData.Frames.OneQuill
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {K s0:ℕ}

axiom one_base_product_hit_calendar (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→ F) (hw:w.moral t z)
    (M:ℕ) (h:OneUnaryParameters p M K s0) (hM:4≤ M) (C:ℝ) (k:ℕ)
    (ε:ℝ) (hε:0<ε):
    ∃ α c:ℝ,0<α ∧ 0< c ∧ ∀ᶠ n:ℕ in atTop,let N:=M* n;
      ∀ (m:Mixer p n) (u:Wgt (OneUnit p n N)),IsLaw u →
      oneBySide u m (bp ((1/32:ℝ)* n)) →
      (∀ x,u x≤ bp (C*(2* N))* oneUnitRaw m N x) →
      Fintype.card (Row p n)+2* p.h+3≤ N → unaryGood m K s0 → reducedBinaryGood m →
      ∀ H:OneKeys t N→ Prop,OneDesign t (fun x=> ind (H x)) k →
      ε≤ pr (oneLawNu p N t z) H →
      pr u (fun o=>¬OneBaseSober w t z K H m α o)≤ bp (-c* n)

end

end Lax793645.BaseQueryHits
