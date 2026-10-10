import Lax342547.ResidualRealization
import Lax342547Proofs.RankedProjection

namespace Lax342547Proofs.ResidualRealization

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces

open Lax342547.ResidualRealization

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.ResidualRealization.matrixPair_sub
---
-/
theorem matrixPair_sub {B : Type} [Fintype B] (M Q : Matrix B B Binary) :
    matrixPair (M - Q) = matrixPair M - matrixPair Q :=
  (matrixPairing (I := B)).map_sub M Q

/--
---
conclusion: Lax342547.ResidualRealization.matrix_response_sub
---
-/
theorem matrix_response_sub {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (M Q : Fin 2 → Comp → Matrix B B Binary) :
    matrixResponse X (M - Q) = matrixResponse X M - matrixResponse X Q := by
  classical
  simp [matrixResponse, matrixPair_sub, LinearMap.sub_comp, Finset.sum_sub_distrib]

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

/--
---
conclusion: Lax342547.ResidualRealization.projected_target
---
-/
theorem projected_target (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    {K : ℕ} (hK : P.rank ≤ K)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (M : Fin 2 → Component (Tag k) → Moment k n b degree) :
    ∃ (Q : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β : Lax342547.PureObstructions.Parameters W P U V),
      Lax342547.PureObstructions.response W P U V β = matrixResponse (Profile k n b degree) Q ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β e)) ≤ ∑ i, (M i e).rank) ∧
      ∀ i e, (M i e - Q i e).rank ≤ 2 * K + 28 ∧ (Q i e).rank ≤ (M i e).rank := by
  classical
  have h : ∀ e, ∃ (A C : Fin 2 → Moment k n b degree)
      (β : (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
        (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary] Binary),
      pureResponse (barred W P (U e) (e, true)) (barred W P (V e) (e, false)) β =
        ∑ i, (matrixPair ((A i).transpose * M i e * C i)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ ∑ i, (M i e).rank ∧
      ∀ i, (M i e - (A i).transpose * M i e * C i).rank ≤ 2 * K + 28 ∧
        ((A i).transpose * M i e * C i).rank ≤ (M i e).rank := by
    intro e
    exact Lax342547Proofs.RankedProjection.actual_pure_projection W P hK (U e) (V e) e (fun i => M i e)
  choose A C β hβ hrβ hr using h
  let Q := fun i e => (A e i).transpose * M i e * C e i
  refine ⟨Q, β, ?_, hrβ, fun i e => hr e i⟩
  apply LinearMap.ext
  intro x
  simp only [Lax342547.PureObstructions.response, hβ, matrixResponse,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Lax342547.PureObstructions.endpointComponent]
  exact Finset.sum_comm

/--
---
conclusion: Lax342547.ResidualRealization.baseline_response
---
-/
theorem baseline_response
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2) :
    matrixResponse (Profile k n b degree) (baselineMatrices F z) =
      ∑ i, (fullContraction F (Profile k n b degree) i z).comp (LinearMap.proj i) := by
  rfl

/--
---
conclusion: Lax342547.ResidualRealization.derivative_response
---
-/
theorem derivative_response (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    matrixResponse (Profile k n b degree) (derivativeMatrices W P Q U V F z δ ε) =
      response W P Q U V F z δ ε := by
  classical
  apply LinearMap.ext
  intro x
  simp only [matrixResponse, derivativeMatrices, Lax342547Proofs.ResponseSolvability.matrixPair_add,
    response, componentResponse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.proj_apply, Submodule.subtype_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  change matrixPair (coefficients _ _) ((x i).val e) + matrixPair (coefficients _ _) ((x i).val e) = _
  change _ = matrixPair (coefficients _ _) ((x i).val e) + matrixPair (coefficients _ _) ((x i).val e)
  exact add_comm _ _

/--
---
conclusion: Lax342547.ResidualRealization.product_response
---
-/
theorem product_response (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    Lax342547.PureObstructions.response W P U V (extraFamily W P Q U V z δ ε) =
      matrixResponse (Profile k n b degree) (productMatrices W P Q U V z δ ε) := by
  classical
  apply LinearMap.ext
  intro x
  simp only [Lax342547.PureObstructions.response, extraFamily,
    Lax342547Proofs.ResponseMatrices.extra_product_response, matrixResponse, productMatrices,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Lax342547.PureObstructions.endpointComponent]
  exact Finset.sum_comm

omit [Fintype H] in
/--
---
conclusion: Lax342547.ResidualRealization.pure_response_sub
---
-/
theorem pure_response_sub (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (β γ : Lax342547.PureObstructions.Parameters W P U V) :
    Lax342547.PureObstructions.response W P U V (β - γ) =
      Lax342547.PureObstructions.response W P U V β - Lax342547.PureObstructions.response W P U V γ := by
  let f : Lax342547.PureObstructions.Parameters W P U V →ₗ[Binary]
      Module.Dual Binary (Fin 2 → Profile k n b degree) :=
    { toFun := Lax342547.PureObstructions.response W P U V
      map_add' := Lax342547Proofs.ResponseSolvability.pure_family_add W P U V
      map_smul' := Lax342547Proofs.ResponseSolvability.pure_family_smul W P U V }
  exact f.map_sub β γ

/--
---
conclusion: Lax342547.ResidualRealization.bounded_remainder
---
-/
theorem bounded_remainder {K : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Bounded F K) (z : Fin 2)
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (β : Lax342547.PureObstructions.Parameters W P U V)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z)
    (hδ : ∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28)
    (hsol : fullResponse W P Q U V F z β δ ε = matrixResponse (Profile k n b degree) M -
      ∑ i, (fullContraction F (Profile k n b degree) i z).comp (LinearMap.proj i)) :
    ∃ (M0 R0 : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β0 β1 : Lax342547.PureObstructions.Parameters W P U V),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V β1 = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      β0 + β1 + extraFamily W P Q U V z δ ε = β := by
  classical
  obtain ⟨M0, β0, hβ0, hrβ0, hr0⟩ := projected_target W P hK U V M
  let β1 := β - β0 - extraFamily W P Q U V z δ ε
  let R0 := M - M0 - baselineMatrices F z - derivativeMatrices W P Q U V F z δ ε -
    productMatrices W P Q U V z δ ε
  refine ⟨M0, R0, β0, β1, hβ0, hrβ0, fun i e => (hr0 i e).2, ?_, ?_, ?_⟩
  · simp only [β1, pure_response_sub, hβ0, product_response, R0, matrix_response_sub]
    rw [baseline_response, derivative_response]
    unfold fullResponse at hsol
    rw [eq_sub_of_add_eq hsol]
    abel
  · intro i e
    have hplus := (Lax342547Proofs.ResponseMatrices.baseline_coordinate_rank F e z (3 * K + 28)
      (hF e z).1 (hF e z).2.2.2 i).1
    have hd := (Lax342547Proofs.ResponseMatrices.restriction_rank
      (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i).trans (hδ e)
    have hr := Lax342547Proofs.ResponseMatrices.bounded_residual_rank K (M i e) (M0 i e)
      (hr0 i e).1 (fullPlus F e i z) (fullMinus F e i z)
      (restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i)
      (restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε e) i) hplus hd
    simpa only [R0, Pi.sub_apply, baselineMatrices, derivativeMatrices, productMatrices,
      residualCoefficients, sub_add_eq_sub_sub] using hr
  · dsimp [β1]
    abel

/--
---
conclusion: Lax342547.ResidualRealization.paired_matrix_representation
---
-/
theorem paired_matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (t : Fin 2 → Module.Dual Binary X) :
    ∃ M : Fin 2 → Comp → Matrix B B Binary,
      matrixResponse X M = ∑ i, (t i).comp (LinearMap.proj i) := by
  classical
  have h : ∀ i, ∃ M : Comp → Matrix B B Binary,
      ∀ x : X, t i x = ∑ e, matrixPair (M e) (x.val e) := by
    intro i
    exact Lax342547Proofs.ResponseMatrices.matrix_representation X (t i)
  choose M hM using h
  refine ⟨M, ?_⟩
  apply LinearMap.ext
  intro x
  simp only [matrixResponse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]
  exact Finset.sum_congr rfl (fun i _ => (hM i (x i)).symm)

/--
---
conclusion: Lax342547.ResidualRealization.recipe_remainder
---
-/
theorem recipe_remainder [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hF : Extends F T) (hbounded : Bounded F K)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R
      (Lax342547.PairedRecipes.endpointAtoms W i) (Lax342547.PairedRecipes.oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2)
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (hM : matrixResponse (Profile k n b degree) M =
      ∑ i, (D.role + gradient D L R (leftWitness W i z)).comp (LinearMap.proj i)) :
    ∃ (M0 R0 : Fin 2 → Component (Tag k) → Moment k n b degree)
      (β0 β1 : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V β1 = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28) ∧
      fullResponse W P Q U V F z (β0 + β1 + extraFamily W P Q U V z δ ε) δ ε =
        ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i) := by
  classical
  obtain ⟨β, δ, ε, hsol, hbound⟩ :=
    Lax342547Proofs.BoundedDerivatives.bounded_recipe_solution hk W D L R oA oB P Q hK
      A B hA hfresh U V hU hV T hT F hF hbounded hrecipe hfrozen hkeys hgradients hdegree z
  have htarget : fullResponse W P Q U V F z β δ ε = matrixResponse (Profile k n b degree) M -
      ∑ i, (fullContraction F (Profile k n b degree) i z).comp (LinearMap.proj i) := by
    rw [hsol, hM]
    simp only [Lax342547.RecipeResiduals.residual, LinearMap.sub_comp, Finset.sum_sub_distrib]
  obtain ⟨M0, R0, β0, β1, h0, hrβ0, hr0, h1, hr1, he⟩ :=
    bounded_remainder W P Q hK U V F hbounded z M β δ ε (fun e => (hbound e).1) htarget
  refine ⟨M0, R0, β0, β1, δ, ε, h0, hrβ0, hr0, h1, hr1, hbound, ?_⟩
  rw [he]
  exact hsol

end Lax342547Proofs.ResidualRealization
