import Lax342547.SelectorInterpolation
import Lax342547.Walsh
import Lax342547.FiniteSampling

/-!
---
title: Boolean polynomial nonvanishing and exactification
type: lemma
---
Finite differences of the actual bounded-degree selector span prove its uniform nonzero mass, exactification below that threshold, and recovery across excluded labels.
-/

namespace Lax342547.BooleanWeight

open Lax342547.MomentSpace Lax342547.SelectorInterpolation
open scoped BigOperators

noncomputable def flip {b : ℕ} (i : Fin b) (x : Fin b → Binary) : Fin b → Binary :=
  Function.update x i (x i+1)

noncomputable def derivative {b : ℕ} (i : Fin b) (f : (Fin b → Binary) → Binary) :
    (Fin b → Binary) → Binary := fun x => f x+f (flip i x)

noncomputable def weight {b : ℕ} (f : (Fin b → Binary) → Binary) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => f x ≠ 0)).card

axiom flip_twice {b : ℕ} (i : Fin b) (x : Fin b → Binary) : flip i (flip i x) = x

axiom derivative_monomial {b : ℕ} (i : Fin b) (S : Finset (Fin b)) :
    derivative i (monomial S) = if i ∈ S then monomial (S.erase i) else 0

axiom derivative_degree {b d : ℕ} (i : Fin b) (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b (d+1)) : derivative i f ∈ selectorSpan b d

axiom invariant_constant {b : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : ∀ i x, f (flip i x) = f x) : ∀ x y, f x = f y

axiom derivative_weight {b : ℕ} (i : Fin b) (f : (Fin b → Binary) → Binary) :
    weight (derivative i f) ≤ 2*weight f

axiom constant_weight {b : ℕ} (c : Binary) (hc : c ≠ 0) :
    weight (fun _ : Fin b → Binary => c) = 2^b

axiom nonzero_weight {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (hne : f ≠ 0) : 2^b ≤ 2^d*weight f

axiom uniform_nonzero_mass {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (hne : f ≠ 0) :
    1/(2 : ℝ)^d ≤ Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0)

axiom uniform_error_exactification {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d)
    (herr : Lax342547.RetainedImages.cellMass (fun _ : Fin b → Binary => 1/(2 : ℝ)^b)
      (fun x => f x ≠ 0) < 1/(2 : ℝ)^d) : f = 0

axiom excluded_labels_exactification {b d : ℕ} (f : (Fin b → Binary) → Binary)
    (hf : f ∈ selectorSpan b d) (E : Finset (Fin b → Binary))
    (hzero : ∀ x, x ∉ E → f x = 0) (hE : 2^d*E.card < 2^b) : f = 0

end Lax342547.BooleanWeight
