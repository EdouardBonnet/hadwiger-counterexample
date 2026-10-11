import Lax342547.PairedAnnihilators
import Lax342547.TensorAnnihilators

namespace Lax342547Proofs.PairedAnnihilators

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.ProjectedPins Lax342547.TableSpaces Lax342547.TensorAnnihilators
open Lax342547.PairedAnnihilators

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.PairedAnnihilators.endpoint_projection
---
The individual quotient maps descend through the nominal quotients.
Pull back an arbitrary individual bilinear form. Its other endpoint
block is zero, leaving exactly the desired individual tensor test.
-/
theorem endpoint_projection {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (S T : Submodule Binary (B → Binary))
    (hD : D.map (primalProjection i) ≤ S) (hE : E.map (primalProjection i) ≤ T) :
    PureAnnihilates (M i) S T := by
  classical
  intro γ
  have hDker : D ≤ LinearMap.ker (S.mkQ.comp (primalProjection (H := H) i)) := by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hD ⟨v, hv, rfl⟩)
  have hEker : E ≤ LinearMap.ker (T.mkQ.comp (primalProjection (H := H) i)) := by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero T).mpr (hE ⟨v, hv, rfl⟩)
  let f := D.liftQ (S.mkQ.comp (primalProjection i)) hDker
  let g := E.liftQ (T.mkQ.comp (primalProjection i)) hEker
  let β := γ.compl₁₂ f g
  have hproj (j : Fin 2) (v : B → Binary) :
      primalProjection (H := H) i (primalEmbedding j v) = if j = i then v else 0 := by
    ext b
    simp [primalProjection, primalEmbedding, eq_comm]
    split_ifs <;> rfl
  have hb (j : Fin 2) :
      β.compl₁₂ (D.mkQ.comp (primalEmbedding j)) (E.mkQ.comp (primalEmbedding j)) =
        if j = i then γ.compl₁₂ S.mkQ T.mkQ else 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change γ (S.mkQ (primalProjection i (primalEmbedding j v)))
      (T.mkQ (primalProjection i (primalEmbedding j w))) = _
    rw [hproj, hproj]
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  have hh := h β
  change (∑ j, matrixPair (LinearMap.BilinForm.toMatrix'
    (β.compl₁₂ (D.mkQ.comp (primalEmbedding j))
      (E.mkQ.comp (primalEmbedding j)))) (M j)) = 0 at hh
  simp only [hb] at hh
  fin_cases i <;> simpa [pureContraction, matrixPair] using hh

/--
---
conclusion: Lax342547.PairedAnnihilators.endpoint_rank
---
Individual pure annihilation costs only the dimensions of the individual
primal quotient kernels, independently of the nominal channel dimension.
-/
theorem endpoint_rank {B H : Type} [Fintype B] [DecidableEq B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (S T : Submodule Binary (B → Binary))
    (hD : D.map (primalProjection i) ≤ S) (hE : E.map (primalProjection i) ≤ T) :
    (M i).rank ≤ Module.finrank Binary S + Module.finrank Binary T :=
  Lax342547.TensorAnnihilators.pure_rank (M i) S T (Lax342547.PairedAnnihilators.endpoint_projection M D E h i S T hD hE)

end Lax342547Proofs.PairedAnnihilators
