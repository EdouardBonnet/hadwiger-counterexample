import Lax342547.BoundedDerivatives
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Lax342547.ResponseSolvability

namespace Lax342547Proofs.BoundedDerivatives

open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.BoundedDerivatives.observed_projection
---
Choose a linear section of the observation map onto its range. Composing that section with the observation map preserves all observations and bounds the new image dimension by the observation rank.
-/
theorem observed_projection {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V]
    (L : V →ₗ[Binary] X) :
    ∃ p : V →ₗ[Binary] V, L.comp p = L ∧
      Module.finrank Binary (LinearMap.range p) ≤ Module.finrank Binary (LinearMap.range L) := by
  obtain ⟨s, hs⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let p := s.comp L.rangeRestrict
  refine ⟨p, ?_, ?_⟩
  · ext v
    have hv := DFunLike.congr_fun hs (L.rangeRestrict v)
    exact congrArg Subtype.val hv
  · have hle : LinearMap.range p ≤ LinearMap.range s := by
      rintro _ ⟨v, rfl⟩
      exact ⟨L.rangeRestrict v, rfl⟩
    calc
      _ ≤ Module.finrank Binary (LinearMap.range s) := Submodule.finrank_mono hle
      _ ≤ Module.finrank Binary (LinearMap.range L) := LinearMap.finrank_range_le s

open Lax342547.ChannelChanges

/--
---
conclusion: Lax342547.BoundedDerivatives.allowed_projection
---
Observe an allowed channel vector only through its pairings with the baseline image. This observation factors through the baseline dual map. A section onto its image therefore gives a projection inside the same allowed value space with rank at most the baseline rank.
-/
theorem allowed_projection {H X : Type} [Fintype H]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (G : X →ₗ[Binary] (H → Binary)) :
    ∃ p : perpendicular S →ₗ[Binary] perpendicular S,
      (∀ c x, dotProduct (p c).val (G x) = dotProduct c.val (G x)) ∧
      Module.finrank Binary (LinearMap.range p) ≤ Module.finrank Binary (LinearMap.range G) := by
  let L := G.dualMap.comp ((dotProductBilin Binary Binary).comp (perpendicular S).subtype)
  obtain ⟨p, hp, hr⟩ := Lax342547.BoundedDerivatives.observed_projection L
  refine ⟨p, ?_, ?_⟩
  · intro c x
    have he := DFunLike.congr_fun hp c
    exact DFunLike.congr_fun he x
  · have hle : LinearMap.range L ≤ LinearMap.range G.dualMap := by
      rintro _ ⟨c, rfl⟩
      exact ⟨(dotProductBilin Binary Binary) c.val, rfl⟩
    calc
      _ ≤ Module.finrank Binary (LinearMap.range L) := hr
      _ ≤ Module.finrank Binary (LinearMap.range G.dualMap) := Submodule.finrank_mono hle
      _ = Module.finrank Binary (LinearMap.range G) :=
        LinearMap.finrank_range_dualMap_eq_finrank_range G

/--
---
conclusion: Lax342547.BoundedDerivatives.bounded_derivative
---
Postcompose the derivative map with the allowed value projection. All observed dot products are preserved and the derivative image lies in the bounded-dimensional projection image.
-/
theorem bounded_derivative {D H X : Type} [AddCommGroup D] [Module Binary D]
    [Fintype H] [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (G : X →ₗ[Binary] (H → Binary))
    (δ : D →ₗ[Binary] perpendicular S) :
    ∃ δ' : D →ₗ[Binary] perpendicular S,
      (∀ v x, dotProduct (δ' v).val (G x) = dotProduct (δ v).val (G x)) ∧
      Module.finrank Binary (LinearMap.range δ') ≤ Module.finrank Binary (LinearMap.range G) := by
  obtain ⟨p, hp, hr⟩ := Lax342547.BoundedDerivatives.allowed_projection S G
  refine ⟨p.comp δ, ?_, ?_⟩
  · intro v x
    exact hp (δ v) x
  · have hle : LinearMap.range (p.comp δ) ≤ LinearMap.range p := by
      rintro _ ⟨v, rfl⟩
      exact ⟨δ v, rfl⟩
    exact (Submodule.finrank_mono hle).trans hr

/--
---
conclusion: Lax342547.BoundedDerivatives.bounded_derivative_covectors
---
Convert baseline covectors into their coordinate vectors. Coordinate conversion cannot increase rank; apply the allowed derivative replacement to this actual observation map.
-/
theorem bounded_derivative_covectors {D H X : Type} [AddCommGroup D] [Module Binary D]
    [Fintype H] [DecidableEq H] [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (S : Submodule Binary (H → Binary)) (C : X →ₗ[Binary] Module.Dual Binary (H → Binary))
    (δ : D →ₗ[Binary] perpendicular S) :
    ∃ δ' : D →ₗ[Binary] perpendicular S,
      (∀ v x, dotProduct (δ' v).val (Lax342547.TensorAnnihilators.dualCoordinates (C x)) =
        dotProduct (δ v).val (Lax342547.TensorAnnihilators.dualCoordinates (C x))) ∧
      Module.finrank Binary (LinearMap.range δ') ≤ Module.finrank Binary (LinearMap.range C) := by
  let G := Lax342547.TensorAnnihilators.dualCoordinates.comp C
  obtain ⟨δ', hp, hr⟩ := Lax342547.BoundedDerivatives.bounded_derivative S G δ
  refine ⟨δ', hp, hr.trans ?_⟩
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

open Lax342547.PairedAnnihilators Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.NominalPrimal Lax342547.TensorAnnihilators
open Lax342547.BarredSpaces

def primalInput {B H : Type} (i : Fin 2) (v : B → Binary) : primal (B := B) (H := H) :=
  ⟨primalEmbedding i v, by intro j h; simp [primalEmbedding]⟩

/--
---
conclusion: Lax342547.BoundedDerivatives.bounded_component
---
Use the full combined primal spaces for both reciprocal baseline maps. Their bounded covector ranks control the two replacement derivatives. Coordinate matrix tests prove that every component response is unchanged for arbitrary input matrices.
-/
theorem bounded_component {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (R : ℕ)
    (hplus : Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hminus : Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    ∃ δ' ε', componentResponse F e z D E S T δ' ε' = componentResponse F e z D E S T δ ε ∧
      Module.finrank Binary (LinearMap.range δ') ≤ R ∧
      Module.finrank Binary (LinearMap.range ε') ≤ R := by
  classical
  let Cplus := (F.forward e).compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z)
  let Cminus := (F.reverse e).flip.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z)
  obtain ⟨δ', hδ, hrδ⟩ := Lax342547.BoundedDerivatives.bounded_derivative_covectors S Cminus δ
  obtain ⟨ε', hε, hrε⟩ := Lax342547.BoundedDerivatives.bounded_derivative_covectors T Cplus ε
  refine ⟨δ', ε', ?_, hrδ.trans hminus, hrε.trans hplus⟩
  have hG : ∀ i, Lax342547.TensorContractions.ambient (fullPlus F e i z) (restriction E T ε' i) =
      Lax342547.TensorContractions.ambient (fullPlus F e i z) (restriction E T ε i) := by
    intro i
    unfold Lax342547.TensorContractions.ambient
    congr 1
    ext a b
    simp only [LinearMap.BilinForm.toMatrix'_apply, LinearMap.compl₁₂_apply]
    have hh := hε (E.mkQ (primalEmbedding i (Pi.single b 1)))
      (primalInput (H := H) i (Pi.single a 1))
    change dotProduct (fullPlus F e i z (Pi.single a 1))
      (ε' (E.mkQ (primalEmbedding i (Pi.single b 1)))).val =
      dotProduct (fullPlus F e i z (Pi.single a 1))
        (ε (E.mkQ (primalEmbedding i (Pi.single b 1)))).val
    change dotProduct (ε' (E.mkQ (primalEmbedding i (Pi.single b 1)))).val
      (fullPlus F e i z (Pi.single a 1)) =
      dotProduct (ε (E.mkQ (primalEmbedding i (Pi.single b 1)))).val
        (fullPlus F e i z (Pi.single a 1)) at hh
    simpa only [dotProduct_comm] using hh
  have hF : ∀ i, Lax342547.TensorContractions.ambient (restriction D S δ' i) (fullMinus F e i z) =
      Lax342547.TensorContractions.ambient (restriction D S δ i) (fullMinus F e i z) := by
    intro i
    unfold Lax342547.TensorContractions.ambient
    congr 1
    ext a b
    simp only [LinearMap.BilinForm.toMatrix'_apply, LinearMap.compl₁₂_apply]
    exact hδ (D.mkQ (primalEmbedding i (Pi.single a 1)))
      (primalInput (H := H) i (Pi.single b 1))
  simp only [componentResponse, hG, hF]

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.CutProfiles Lax342547.ExactPins Lax342547.PairedWitnesses Lax342547.RawBaselines

/--
---
conclusion: Lax342547.BoundedDerivatives.bounded_response
---
Choose the two bounded derivatives independently in every component. The component identities preserve the full response on the actual cut-profile pair space. Both derivative ranks are at most three times the pin budget plus twenty-eight.
-/
theorem bounded_response {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Bounded F K) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z) :
    ∃ δ' ε', response W P Q U V F z δ' ε' = response W P Q U V F z δ ε ∧
      ∀ e, Module.finrank Binary (LinearMap.range (δ' e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε' e)) ≤ 3 * K + 28 := by
  classical
  have h : ∀ e, ∃ δ' ε', componentResponse F e z
      (barred W P (U e) (e, true)) (barred W P (V e) (e, false))
      (protectedChannel Q z (e, false)) (protectedChannel Q z (e, true)) δ' ε' =
        componentResponse F e z (barred W P (U e) (e, true)) (barred W P (V e) (e, false))
          (protectedChannel Q z (e, false)) (protectedChannel Q z (e, true)) (δ e) (ε e) ∧
      Module.finrank Binary (LinearMap.range δ') ≤ 3 * K + 28 ∧
      Module.finrank Binary (LinearMap.range ε') ≤ 3 * K + 28 := by
    intro e
    exact Lax342547.BoundedDerivatives.bounded_component F e z _ _ _ _ (3 * K + 28) (hF e z).1 (hF e z).2.2.2 (δ e) (ε e)
  choose δ' ε' heq hrδ hrε using h
  refine ⟨δ', ε', ?_, fun e => ⟨hrδ e, hrε e⟩⟩
  simp only [response, heq]

open Lax342547.PairedRecipes Lax342547.PinLabelExclusions

/--
---
conclusion: Lax342547.BoundedDerivatives.bounded_recipe_solution
---
Start from the proved unrestricted solution of the actual scalar recipe. Replace its two derivative families with bounded-rank families while preserving the pure response and every derivative contraction. This retains the whole-space linearized solution with the paper baseline rank bound.
-/
theorem bounded_recipe_solution {H N : Type} [Fintype H] [Fintype N] {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (hbounded : Bounded F K)
    (hrecipe : ScalarRecipe W D L R oA oB T A B)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (hgradients : ∀ i, Lax342547.ConcreteRecipes.RecipeGradients D L R (endpointAtoms W i) (oppositeP W oB i))
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) (z : Fin 2) :
    ∃ (β : Lax342547.PureObstructions.Parameters W P U V)
      (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z), fullResponse W P Q U V F z β δ ε =
      ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i) ∧
      ∀ e, Module.finrank Binary (LinearMap.range (δ e)) ≤ 3 * K + 28 ∧
        Module.finrank Binary (LinearMap.range (ε e)) ≤ 3 * K + 28 := by
  obtain ⟨β, δ, ε, hsol⟩ := Lax342547.ResponseSolvability.recipe_solution hk W D L R oA oB P Q
    hK A B hA hfresh U V hU hV T hT F hF hrecipe hfrozen hkeys hgradients hdegree z
  obtain ⟨δ', ε', heq, hr⟩ := Lax342547.BoundedDerivatives.bounded_response W P Q U V F hbounded z δ ε
  refine ⟨β, δ', ε', ?_, hr⟩
  rw [fullResponse, heq]
  exact hsol

end Lax342547Proofs.BoundedDerivatives
