import Lax793645.TriangleFreeHoles

namespace Lax793645Proofs.Manuscript.TriangleFreeHoles

/--
---
conclusion: Lax793645.TriangleFreeHoles.triangle_free
---
Sum the two functional evaluations at each of the three vertices. The shared
ambient vectors cancel in pairs. The symmetric terms cancel too, leaving
one copy of each edge parity.
-/
theorem triangle_free {I X V : Type*} (U : I → X → V) (u : I → V → ZMod 2)
    (a : X → ZMod 2) (T : X → X → ZMod 2)
    (injective : ∀ i, Function.Injective (U i)) (symm : ∀ x y, T x y = T y x) :
    let H := Lax793645.Holes.relation U u a T
    (∀ i j, H i j → H j i) ∧ (∀ i, ¬H i i) ∧
      ∀ i j k, H i j → H j k → ¬H i k := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rintro i j ⟨x, y, hxy, hx, hy, h⟩
    exact ⟨y, x, hxy.symm, hy, hx, (add_comm _ _).trans h⟩
  · rintro i ⟨x, y, hxy, _, _, h⟩
    obtain rfl := injective i hxy
    exact zero_ne_one (by simpa only [ZModModule.add_self] using h)
  · rintro i j k ⟨x, y, hxy, hx, hy, p⟩ ⟨z, w, hzw, hz, hw, q⟩
      ⟨v, t, hvt, hv, ht, r⟩
    have e₁ := (hy z).symm.trans ((congrArg (u i) hzw).trans (ht w))
    have e₂ := (hx v).symm.trans ((congrArg (u j) hvt).trans (hw t))
    have e₃ := (hv x).symm.trans ((congrArg (u k) hxy).trans (hz y))
    rw [symm t w] at e₁
    rw [symm v x, symm z y] at e₃
    have h : (a x + a y) + (a z + a w) + (a v + a t) = 0 := by
      have cancel {b c : ZMod 2} (hbc : b = c) : b + c = 0 := hbc ▸ ZModModule.add_self c
      calc
        _ = ((a z + T y z) + (a w + T w t)) +
            ((a v + T x v) + (a t + T w t)) +
            ((a x + T x v) + (a y + T y z)) := by
          rw [show ((a z + T y z) + (a w + T w t)) +
               ((a v + T x v) + (a t + T w t)) +
               ((a x + T x v) + (a y + T y z)) =
               ((a x + a y) + (a z + a w) + (a v + a t)) +
               (T y z + T y z) + (T w t + T w t) + (T x v + T x v) by ac_rfl]
          simp only [ZModModule.add_self, add_zero]
        _ = 0 := by rw [cancel e₁, cancel e₂, cancel e₃]; simp
    rw [p, q, r, ZModModule.add_self, zero_add] at h
    exact one_ne_zero h

end Lax793645Proofs.Manuscript.TriangleFreeHoles
