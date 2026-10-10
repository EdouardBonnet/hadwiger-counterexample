import Lax342547.PinLabelExclusions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
---
title: Extracting fresh label coefficients through pin quotients
type: theorem
---
The stronger sparse exclusion permits a selected coefficient to be read
from the quotient by a projected pin. This is a first ingredient for
isolating selected blocks in the §6 annihilator argument. The extractor
also descends through selected key spans after quotienting its output
by the corresponding base ray. Applying it to the actual label summands
remains a separate step.
-/

namespace Lax342547.QuotientExtractors

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.SparsePins Lax342547.PinLabelExclusions

axiom quotient_factor {C V W : Type}
    [AddCommGroup C] [Module Binary C] [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] (D : Submodule Binary V)
    (f : C →ₗ[Binary] V) (g : C →ₗ[Binary] W)
    (h : ∀ c, f c ∈ D → g c = 0) :
    ∃ q : (V ⧸ D) →ₗ[Binary] W, q.comp (D.mkQ.comp f) = g

axiom pin_extractor {Base Comp H N : Type} {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R + 14) (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i) :
    ∃ q : ((SelectorCoordinates b degree × Option Base → Binary) ⧸ projected P i a) →ₗ[Binary]
        (Option Base → Binary),
      ∀ t ∈ L, ∀ v : Option Base → Binary,
        q ((projected P i a).mkQ (labelTensor (selectorEval (degree := degree)) t v)) =
          if t = s then v else 0

axiom key_extractor {Base Comp H N I : Type} {b degree R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R + 14) (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i)
    (label : I → Fin b → Binary) (base : I → Option Base → Binary)
    (hlabels : ∀ j, label j ∈ L) (Ray : Submodule Binary (Option Base → Binary))
    (hmatch : ∀ j, label j = s → base j ∈ Ray) :
    ∃ q : ((SelectorCoordinates b degree × Option Base → Binary) ⧸
        (projected P i a ⊔ Submodule.span Binary
          (Set.range (fun j => labelTensor (selectorEval (degree := degree)) (label j) (base j))))) →ₗ[Binary]
        ((Option Base → Binary) ⧸ Ray),
      ∀ t ∈ L, ∀ v : Option Base → Binary,
        q (Submodule.Quotient.mk (labelTensor (selectorEval (degree := degree)) t v)) =
          if t = s then Ray.mkQ v else 0

end Lax342547.QuotientExtractors
