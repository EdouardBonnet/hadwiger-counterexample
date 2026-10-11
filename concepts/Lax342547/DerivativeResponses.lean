import Lax342547.ChannelChanges
import Lax342547.SelectedRemoval
import Lax342547.ResidualLabels

/-!
---
title: The full linearized response on pairs of actual cut profiles
type: lemma
---
The two allowed derivative families factor through the actual barred
nominal quotients and take values perpendicular to the opposite pin's
protected channels. Their contractions with the fixed baseline maps
are added to the independent pure bilinear response.
-/

namespace Lax342547.DerivativeResponses

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.SelectedRemoval

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

abbrev PlusParameters (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2) :=
  ∀ e, (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
    perpendicular (protectedChannel Q z (e, false))

abbrev MinusParameters (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) (z : Fin 2) :=
  ∀ e, (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary]
    perpendicular (protectedChannel Q z (e, true))

def restriction {B : Type} (D : Submodule Binary (Nominal B H))
    (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) :=
  (((perpendicular S).subtype.comp δ).comp D.mkQ).comp (primalEmbedding i)

noncomputable def componentResponse {Comp B : Type} [Fintype B]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δF : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (δG : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    (Fin 2 → Matrix B B Binary) →ₗ[Binary] Binary :=
  ∑ i, (TensorContractions.ambient (fullPlus F e i z) (restriction E T δG i) +
    TensorContractions.ambient (restriction D S δF i) (fullMinus F e i z)).comp (LinearMap.proj i)

noncomputable def response (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δF : PlusParameters W P Q U z) (δG : MinusParameters W P Q V z) :
    (Fin 2 → Profile k n b degree) →ₗ[Binary] Binary :=
  ∑ e, (componentResponse F e z (barred W P (U e) (e, true))
    (barred W P (V e) (e, false)) (protectedChannel Q z (e, false))
    (protectedChannel Q z (e, true)) (δF e) (δG e)).comp (PureObstructions.endpointComponent e)

noncomputable def fullResponse (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (β : PureObstructions.Parameters W P U V)
    (δF : PlusParameters W P Q U z) (δG : MinusParameters W P Q V z) :
    (Fin 2 → Profile k n b degree) →ₗ[Binary] Binary :=
  PureObstructions.response W P U V β + response W P Q U V F z δF δG

def Annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) : Prop :=
  ∀ β δF δG, fullResponse W P Q U V F z β δF δG x = 0

axiom pure_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x) :
    Lax342547.PureObstructions.Annihilates W P U V x

axiom derivative_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (δF : PlusParameters W P Q U z) (δG : MinusParameters W P Q V z) :
    response W P Q U V F z δF δG x = 0

axiom atom_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) :
    Annihilates W P Q U V F z (Pi.single i (W.left i u.1 u.2).profile)

axiom selected_part_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P Q U V F z (selectedPart W c)

axiom subtract_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P Q U V F z (x - selectedPart W c)

axiom component_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k))
    (δF : (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
      perpendicular (protectedChannel Q z (e, false)))
    (δG : (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary]
      perpendicular (protectedChannel Q z (e, true))) :
    componentResponse F e z (barred W P (U e) (e, true))
      (barred W P (V e) (e, false)) (protectedChannel Q z (e, false))
      (protectedChannel Q z (e, true)) δF δG (Lax342547.PureObstructions.endpointComponent e x) = 0

axiom unselected_obstruction {K : ℕ} (hk : 0 < k)
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∃ c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary,
    ∃ L : Fin 2 → Component (Tag k) → Finset (Fin b → Binary),
    ∃ Z : Fin 2 → Component (Tag k) → (Fin b → Binary) →
        Matrix (Option (Base k n)) (Option (Base k n)) Binary,
      Annihilates W P Q U V F z (x - selectedPart W c) ∧
      ∀ i e, (L i e).card ≤ 2 * K + 28 ∧
        (∀ s ∈ L i e, s ∉ Lax342547.ResidualLabels.chosenLabels W i ∧
          Lax342547.BaseMoments.IsBaseMoment (Z i e s)) ∧
        (∑ s ∈ L i e, (Z i e s).rank) ≤ 2 * K + 28 ∧
        ((x - selectedPart W c) i).val e =
          ∑ s ∈ L i e, Lax342547.TensorBlocks.block selectorEval s (Z i e s)

axiom right_test (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ)
    (c : H → Binary) (hc : c ∈ perpendicular (protectedChannel Q z (e, true))) :
    dotProduct (fullPlus F e i z
      (((x i).val e).mulVecLin (Lax342547.PrimalContractions.coordinates ψ))) c = 0

axiom plus_contraction_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (Lax342547.ResidualLabels.chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    ((x i).val e).mulVecLin (Lax342547.PrimalContractions.coordinates ψ) = 0

axiom left_test (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker ψ)
    (c : H → Binary) (hc : c ∈ perpendicular (protectedChannel Q z (e, false))) :
    dotProduct (fullMinus F e i z
      (((x i).val e).transpose.mulVecLin (Lax342547.PrimalContractions.coordinates ψ))) c = 0

axiom minus_contraction_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hV : ∀ j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (Lax342547.ResidualLabels.chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    ((x i).val e).transpose.mulVecLin (Lax342547.PrimalContractions.coordinates ψ) = 0

end Lax342547.DerivativeResponses
