import Lax793645.ConstructionData

/-!
---
title: A one-sided comparison of overlaps
type: lemma
---
The square of the overlap of two bounded functions is at most the overlap of the
projected actual densities plus the two mean positive excesses of the projected
functions. All averages are finite cell averages.
-/

namespace Lax793645.ProjectedOverlap

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
axiom one_sided_projected_mend
    {A B : Type} [Fintype A] [Fintype B] (ν : Wgt A) (hν : IsLaw ν) (P : A→ B)
    (f g d e : Wgt A) (hf : bower f) (hg : bower g)
    (hd : ∀ x,0≤ d x) (he : ∀ x,0≤ e x) :
    dip ν f g^2≤ dip ν (banner ν P d) (banner ν P e)+
      avg ν (fun x=> max (banner ν P f x-banner ν P d x) 0)+
      avg ν (fun x=> max (banner ν P g x-banner ν P e x) 0)

end

end Lax793645.ProjectedOverlap
