import Lax342547.AtomFunctionals
import Mathlib.LinearAlgebra.Dual.Lemmas
import Lax342547.Atoms
import Lax342547.QuadraticDegree
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.AtomFunctionals
open Lax342547.AtomFunctionals

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.CutProfiles Lax342547.SelectorInterpolation
open scoped BigOperators

/--
---
conclusion: Lax342547.AtomFunctionals.atom_local_functional
---
-/
theorem atom_local_functional {k n b degree : ℕ} (l : Tag k)
    (φ : Module.Dual Binary (Profile k n b degree)) :
    ∃ ψ : Module.Dual Binary (Moment k n b degree),∀ s z
      (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz) = ψ (pointMoment selectorEval s z) := by
  obtain ⟨Ψ,hΨ⟩ := Subspace.dualRestrict_surjective (W := LinearMap.range (representationCut k n b degree)) φ
  refine ⟨Ψ.comp (starMatrixMap l),?_⟩
  intro s z hz
  have he : (atom (degree := degree) l s z hz).val = starMatrixMap l (pointMoment selectorEval s z) := by
    funext e
    exact Lax342547.Atoms.atom_component l s z hz e
  have hf := LinearMap.congr_fun hΨ (atom (degree := degree) l s z hz)
  change Ψ (atom (degree := degree) l s z hz).val = φ (atom (degree := degree) l s z hz) at hf
  rw [← hf,he]
  rfl

/--
---
conclusion: Lax342547.AtomFunctionals.cut_star_sum
---
-/
theorem cut_star_sum {k n b degree : ℕ} (w : Tag k → Moment k n b degree) :
    cutMap w = ∑ l,starMatrixMap l (w l) := by
  classical
  funext e
  simp only [Finset.sum_apply]
  change (∑ l ∈ e.val,w l) = ∑ l,if l ∈ e.val then w l else 0
  rw [← Finset.sum_filter]
  simp

/--
---
conclusion: Lax342547.AtomFunctionals.atom_functional_ext
---
-/
theorem atom_functional_ext {k n b degree : ℕ} (φ : Module.Dual Binary (Profile k n b degree))
    (hφ : ∀ l s z (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz) = 0) : φ = 0 := by
  classical
  obtain ⟨Ψ,hΨ⟩ := Subspace.dualRestrict_surjective (W := LinearMap.range (representationCut k n b degree)) φ
  have hzero (l : Tag k) (M : Moment k n b degree) (hM : M ∈ tagSpace k n b degree l) :
      Ψ (starMatrixMap l M) = 0 := by
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨s,z,hz,rfl⟩ := hM
      have he : starMatrixMap l (pointMoment selectorEval s z) = (atom (degree := degree) l s z hz).val := by
        funext e
        exact (Lax342547.Atoms.atom_component l s z hz e).symm
      rw [he]
      have hf := LinearMap.congr_fun hΨ (atom (degree := degree) l s z hz)
      change Ψ (atom (degree := degree) l s z hz).val = φ (atom (degree := degree) l s z hz) at hf
      exact hf.trans (hφ l s z hz)
    | zero => simp
    | add M Q _ _ hM hQ => simp only [map_add,hM,hQ,add_zero]
    | smul c M _ hM => simp only [map_smul,hM,smul_zero]
  ext x
  obtain ⟨w,hw⟩ := x.property
  have hf := LinearMap.congr_fun hΨ x
  change Ψ x.val = φ x at hf
  rw [← hf,← hw]
  change Ψ (cutMap w.val) = 0
  rw [Lax342547.AtomFunctionals.cut_star_sum,map_sum]
  apply Finset.sum_eq_zero
  intro l _
  exact hzero l (w.val l) (w.property l (Set.mem_univ l))

/--
---
conclusion: Lax342547.AtomFunctionals.atom_base_degree
---
-/
theorem atom_base_degree {k n b degree r : ℕ} (l : Tag k) (s : Fin b → Binary)
    (φ : Module.Dual Binary (Profile k n b degree))
    (z : (Fin r → Binary) → Base k n → Binary)
    (hz : ∀ x i,i ∉ allowedBase k n l → z x i = 0)
    (hdegree : ∀ i,(fun x => z x i) ∈ selectorSpan r 1) :
    (fun x => φ (atom (degree := degree) l s (z x) (hz x))) ∈ selectorSpan r 2 := by
  obtain ⟨ψ,hψ⟩ := Lax342547.AtomFunctionals.atom_local_functional l φ
  have hf (i : SelectorCoordinates b degree × Option (Base k n)) :
      (fun x => point selectorEval s (z x) i) ∈ selectorSpan r 1 := by
    apply (selectorSpan r 1).smul_mem (selectorEval s i.1)
    cases i.2 with
    | none => exact Lax342547Proofs.SelectorInterpolation.constant_mem 1 1
    | some j => exact hdegree j
  have hp := Lax342547.QuadraticDegree.linear_outer_product_degree ψ
    (fun i x => point selectorEval s (z x) i) hf
  have he : (fun x => φ (atom (degree := degree) l s (z x) (hz x))) =
      (fun x => ψ (Matrix.of (fun i j => point selectorEval s (z x) i*point selectorEval s (z x) j))) :=
    funext (fun x => hψ s (z x) (hz x))
  rw [he]
  exact hp

end Lax342547Proofs.AtomFunctionals
