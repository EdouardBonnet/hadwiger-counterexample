import Lax342547.CommonAtoms
import Lax342547.ConcreteGeometry

/-!
---
title: An actual common point with diagonal tester one
type: lemma
---
A shared-only point is allowed at every tag and has tester value one whenever the tester has a pair; it removes the common diagonal predictor coefficient.
-/

namespace Lax342547.SharedTesterPoint

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteGeometry
open scoped BigOperators

def sharedTesterPoint {k n : ℕ} : Base k n → Binary
  | Sum.inl _ => 0
  | Sum.inr (q,i) => if q = 0 ∧ i.val < 2 then 1 else 0

axiom shared_point_allowed {k n : ℕ} (l : Tag k) :
    ∀ i,i ∉ allowedBase k n l → sharedTesterPoint (k := k) (n := n) i = 0

axiom shared_point_eta_one {k n b degree r : ℕ} (hr : 2*r ≤ n) (hr0 : 0 < r) (s : Fin b → Binary) :
    eta (k := k) (b := b) (degree := degree) hr (pointMoment selectorEval s sharedTesterPoint) = 1

end Lax342547.SharedTesterPoint
