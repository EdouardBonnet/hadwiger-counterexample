import Lax342547.CompressedResidual
import Lax342547.BaseCompression
import Lax342547.ConstrainedCompression
import Lax342547.QuotientCompression
import Lax342547.RankedProjection
import Lax342547.ResidualRealization
import Lax342547Proofs.ResponseSolvability

namespace Lax342547Proofs.CompressedResidual

open Lax342547.CompressedResidual

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression
open Lax342547.ResidualRealization

/--
---
conclusion: Lax342547.CompressedResidual.compressed_pure_solution
---
-/
theorem compressed_pure_solution {k n b degree r K R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e i, IsCompl (protectedChannel P i (e, true)) (U e i))
    (hV : ∀ e i, IsCompl (protectedChannel P i (e, false)) (V e i))
    (M : Fin 2 → Component (Tag k) → Moment k n b degree)
    (hM : ∀ i e, (M i e).rank ≤ R)
    (β : Lax342547.PureObstructions.Parameters W P U V)
    (hβ : Lax342547.PureObstructions.response W P U V β = matrixResponse (Profile k n b degree) M) :
    ∃ γ : Lax342547.PureObstructions.Parameters W P U V,
      Lax342547.PureObstructions.response W P U V γ = matrixResponse (Profile k n b degree) M ∧
      ∀ e, Module.finrank Binary (LinearMap.range (γ e)) ≤ quotientBound k b degree K R := by
  classical
  have hc : ∀ i : Fin 2, ∃ A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤ blockBound k b degree K R) ∧
      (∀ a v, v ∈ projected P i a ⊔ individualKeys W i a.1 → liftBase (blockMap A) v = v) ∧
      ∀ e, (LinearMap.toMatrix' (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))).transpose *
        M i e * LinearMap.toMatrix' (liftBase (blockMap A)) = M i e := by
    intro i
    exact Lax342547.ConstrainedCompression.actual_block_compression W P hK i (M i) (hM i)
  choose A hr hfix htarget using hc
  let f : Fin 2 → Vector k n b degree →ₗ[Binary] Vector k n b degree :=
    fun i => liftBase (blockMap (A i))
  have hplus : ∀ e, ∃ q : (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
      (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)),
      (∀ v, q ((barred W P (U e) (e, true)).mkQ v) =
        (barred W P (U e) (e, true)).mkQ (nominalLift f v)) ∧
      Module.finrank Binary (LinearMap.range q) ≤ quotientBound k b degree K R := by
    intro e
    exact Lax342547.QuotientCompression.barred_compression W P hK (e, true)
      (U e) (hU e) A hr (fun i v hv => hfix i (e, true) v hv)
  have hminus : ∀ e, ∃ q : (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary]
      (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)),
      (∀ v, q ((barred W P (V e) (e, false)).mkQ v) =
        (barred W P (V e) (e, false)).mkQ (nominalLift f v)) ∧
      Module.finrank Binary (LinearMap.range q) ≤ quotientBound k b degree K R := by
    intro e
    exact Lax342547.QuotientCompression.barred_compression W P hK (e, false)
      (V e) (hV e) A hr (fun i v hv => hfix i (e, false) v hv)
  choose qplus hqplus rqplus using hplus
  choose qminus hqminus rqminus using hminus
  let γ : Lax342547.PureObstructions.Parameters W P U V :=
    fun e => (β e).compl₁₂ (qplus e) (qminus e)
  refine ⟨γ, ?_, fun e => (Lax342547.QuotientCompression.compressed_bilinear_rank
    (β e) (qplus e) (qminus e)).trans (rqplus e)⟩
  apply LinearMap.ext
  intro x
  have hy (i : Fin 2) : (fun e => tensorMap (f i) ((x i).val e)) ∈ Profile k n b degree :=
    Lax342547.BaseCompression.blockMap_profile (A i) ⟨(x i).val, (x i).property, rfl⟩
  let y : Fin 2 → Profile k n b degree := fun i => ⟨_, hy i⟩
  have hresponse : Lax342547.PureObstructions.response W P U V γ x =
      Lax342547.PureObstructions.response W P U V β y := by
    simp only [Lax342547.PureObstructions.response, LinearMap.sum_apply, LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro e _
    exact Lax342547.QuotientCompression.pure_compressed _ _ (β e) f
      (qplus e) (qminus e) (hqplus e) (hqminus e) _
  rw [hresponse, hβ]
  simp only [matrixResponse, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro e _
  exact (Lax342547.BaseCompression.matrixPair_tensorMap (f i) (M i e) _).trans
    (congrArg (fun M => matrixPair M ((x i).val e)) (htarget i e))

/--
---
conclusion: Lax342547.CompressedResidual.compressed_recipe
---
-/
theorem compressed_recipe {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {K : ℕ} {E : Moment k n b degree}
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
      (β0 γ : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z),
      Lax342547.PureObstructions.response W P U V β0 = matrixResponse (Profile k n b degree) M0 ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e)) ≤ ∑ i, (M i e).rank) ∧
      (∀ i e, (M0 i e).rank ≤ (M i e).rank) ∧
      Lax342547.PureObstructions.response W P U V γ = matrixResponse (Profile k n b degree) R0 ∧
      (∀ i e, (R0 i e).rank ≤ 14 * K + 140) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (γ e)) ≤
        quotientBound k b degree K (14 * K + 140)) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (β0 e + γ e)) ≤
        (∑ i, (M i e).rank) + quotientBound k b degree K (14 * K + 140)) ∧
      (∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28) ∧
      fullResponse W P Q U V F z (β0 + γ + extraFamily W P Q U V z δ ε) δ ε =
        ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i) := by
  obtain ⟨M0, R0, β0, β1, δ, ε, h0, hrβ0, hr0, h1, hr1, hd, hfull⟩ :=
    Lax342547.ResidualRealization.recipe_remainder hk W D L R oA oB P Q hK A B hA hfresh
      U V hU hV T hT F hF hbounded hrecipe hfrozen hkeys hgradients hdegree z M hM
  obtain ⟨γ, hγ, hrγ⟩ := Lax342547.CompressedResidual.compressed_pure_solution W P hK U V hU hV R0 hr1 β1 h1
  refine ⟨M0, R0, β0, γ, δ, ε, h0, hrβ0, hr0, hγ, hr1, hrγ, ?_, hd, ?_⟩
  · intro e
    exact (Lax342547.RankedProjection.linear_add_rank _ _).trans
      (Nat.add_le_add (hrβ0 e) (hrγ e))
  · simpa only [fullResponse, Lax342547Proofs.ResponseSolvability.pure_family_add, hγ, h1]
      using hfull

end Lax342547Proofs.CompressedResidual
