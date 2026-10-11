import Lax342547.RecipeChannels
import Lax342547.CompressedResidual
import Lax342547.NonlinearChannels
import Lax342547.TableSpaces
import Lax342547.TargetMatrices

namespace Lax342547Proofs.RecipeChannels
open Lax342547.RecipeChannels

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.ResponseMatrices Lax342547.RawBaselines
open Lax342547.TableSpaces Lax342547.BaseCompression Lax342547.QuotientCompression
open Lax342547.ResidualRealization

open Lax342547.CompressedResidual

/--
---
conclusion: Lax342547.RecipeChannels.nonlinear_recipe
---
-/
theorem nonlinear_recipe {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {K : ℕ} {E : Moment k n b degree}
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (hQ : Q.rank ≤ K) (A B : Fin 2 → Finset (Fin b → Binary))
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
    (hmargin : 28 * copies * Fintype.card (Component (Tag k)) +
      quotientBound k b degree K (14 * K + 140) + 2 * K + 4 * (3 * K + 28) < 970 * r)
    (hchannels : 1000 * r ≤ Fintype.card H) :
    ∃ (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z),
      fullResponse W P Q U V F z (extraFamily W P Q U V z δ ε) δ ε =
        ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i) := by
  classical
  let M := fun i => Lax342547.TargetMatrices.targetMatrix W D L R i z
  have hM := Lax342547.TargetMatrices.target_family_representation W D L R z
    (fun i => hrecipe.odd i z)
  obtain ⟨M0, R0, β0, γ, δ, ε, hβ0, hrβ0, hM0, hγ, hR0, hrγ, hrβ,
    hrδε, hsolution⟩ := Lax342547.CompressedResidual.compressed_recipe hk W D L R oA oB
      P Q hK A B hA hfresh U V hU hV T hT F hF hbounded hrecipe hfrozen hkeys
      hgradients hdegree z M hM
  have hcapacity (e : Component (Tag k)) :
      Module.finrank Binary (LinearMap.range (β0 e + γ e)) + 2 * K + 4 * (3 * K + 28) ≤ Fintype.card H := by
    apply Lax342547.NonlinearChannels.paper_channel_capacity (hmargin := hmargin) (hchannels := hchannels)
    have hsum : (∑ i : Fin 2, (M i e).rank) ≤ 30 * r + 28 * copies * Fintype.card (Component (Tag k)) := by
      have hh : (∑ i : Fin 2, (M i e).rank) ≤
          ∑ _ : Fin 2, (15 * r + 14 * copies * Fintype.card (Component (Tag k))) :=
        by
          dsimp only [M]
          exact Finset.sum_le_sum (fun i _ => Lax342547.TargetMatrices.target_matrix_rank W D L R i z e)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
      nlinarith
    exact (hrβ e).trans (Nat.add_le_add_right hsum _)
  have hprotected (a : Component (Tag k) × Bool) : Module.finrank Binary (protectedChannel Q z a) ≤ K := by
    exact (Finset.single_le_sum (fun a _ => Nat.zero_le (Module.finrank Binary (protectedChannel Q z a)))
      (Finset.mem_univ a)).trans ((Lax342547.TableSpaces.protected_rank Q z).trans hQ)
  have hcomponent (e : Component (Tag k)) := Lax342547.NonlinearChannels.nonlinear_component_correction
    F e z (barred W P (U e) (e, true)) (barred W P (V e) (e, false))
    (protectedChannel Q z (e, false)) (protectedChannel Q z (e, true)) (δ e) (ε e) (β0 e + γ e)
    (hprotected (e, false)) (hprotected (e, true)) (hbounded e z).1 (hbounded e z).2.2.2
    (hrδε e).1 (hrδε e).2 (hcapacity e)
  choose δ' ε' hresponse hproduct using hcomponent
  refine ⟨δ', ε', ?_⟩
  have hprod : extraFamily W P Q U V z δ' ε' = β0 + γ + extraFamily W P Q U V z δ ε := by
    funext e
    exact hproduct e
  have hresp : response W P Q U V F z δ' ε' = response W P Q U V F z δ ε := by
    unfold response
    simp_rw [hresponse]
  unfold fullResponse at hsolution ⊢
  rw [hprod, hresp]
  exact hsolution

end Lax342547Proofs.RecipeChannels
