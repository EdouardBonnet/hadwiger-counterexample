import Lax342547.GradientAssembly
import Lax342547.ChannelAssembly
import Lax342547.NonlinearChannels
import Lax342547.ResponseMatrices

namespace Lax342547Proofs.GradientAssembly
open Lax342547.GradientAssembly

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys
open Lax342547.ResidualRealization Lax342547.NonlinearChannels

/--
---
conclusion: Lax342547.GradientAssembly.contraction_expansion
---
-/
theorem contraction_expansion {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z)
    (hplus : ∀ e i, fullPlus G e i z = fullPlus F e i z +
      restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i)
    (hminus : ∀ e i, fullMinus G e i z = fullMinus F e i z +
      restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε e) i)
    (x : Fin 2 → Profile k n b degree) :
    (∑ i, fullContraction G (Profile k n b degree) i z (x i)) =
      (∑ i, fullContraction F (Profile k n b degree) i z (x i)) +
        fullResponse W P Q U V F z (extraFamily W P Q U V z δ ε) δ ε x := by
  classical
  have hextra (e : Component (Tag k)) := Lax342547.ResponseMatrices.extra_product_response
    (barred W P (U e) (e, true)) (barred W P (V e) (e, false))
    (protectedChannel Q z (e, false)) (protectedChannel Q z (e, true)) (δ e) (ε e)
  simp only [fullContraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply, hplus, hminus,
    Lax342547.NonlinearChannels.ambient_add_expansion]
  simp only [fullResponse, Lax342547.PureObstructions.response, extraFamily, response,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, hextra, componentResponse,
    Lax342547.PureObstructions.endpointComponent, LinearMap.proj_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i e =>
    Lax342547.TensorContractions.ambient (fullPlus F e i z) (fullMinus F e i z) ((x i).val e))]
  simp only [Finset.sum_add_distrib]
  have ha (f g : Vector k n b degree →ₗ[Binary] (H → Binary)) :
      matrixPair (coefficients f g) = Lax342547.TensorContractions.ambient f g := rfl
  simp only [ha]
  abel


/--
---
conclusion: Lax342547.GradientAssembly.corrected_gradients
---
-/
theorem corrected_gradients {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δ : PlusParameters W P Q U z) (ε : MinusParameters W P Q V z)
    (hplus : ∀ e i, fullPlus G e i z = fullPlus F e i z +
      restriction (barred W P (U e) (e, true)) (protectedChannel Q z (e, false)) (δ e) i)
    (hminus : ∀ e i, fullMinus G e i z = fullMinus F e i z +
      restriction (barred W P (V e) (e, false)) (protectedChannel Q z (e, true)) (ε e) i)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (hsolution : fullResponse W P Q U V F z (extraFamily W P Q U V z δ ε) δ ε =
      ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i)) :
    ∀ i x, fullContraction G (Profile k n b degree) i z x =
      (D.role + gradient D L R (leftWitness W i z)) x := by
  classical
  intro i x
  have he := Lax342547.GradientAssembly.contraction_expansion W P Q U V F G z δ ε hplus hminus (Pi.single i x)
  rw [hsolution] at he
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply] at he
  have hsingle (M : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) :
      (∑ j, fullContraction M (Profile k n b degree) j z ((Pi.single i x : Fin 2 → Profile k n b degree) j)) =
        fullContraction M (Profile k n b degree) i z x := by
    fin_cases i <;> simp [Fin.sum_univ_two, Pi.single_apply]
  have hres : (∑ j, Lax342547.RecipeResiduals.residual W D L R F j z ((Pi.single i x : Fin 2 → Profile k n b degree) j)) =
      Lax342547.RecipeResiduals.residual W D L R F i z x := by
    fin_cases i <;> simp [Fin.sum_univ_two, Pi.single_apply]
  rw [hsingle, hsingle, hres] at he
  simp only [Lax342547.RecipeResiduals.residual, LinearMap.sub_apply, LinearMap.add_apply] at he
  rw [he]
  simp only [LinearMap.add_apply]
  abel


/--
---
conclusion: Lax342547.GradientAssembly.simultaneous_gradients
---
-/
theorem simultaneous_gradients {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V U' V' : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (δ : ∀ z, PlusParameters W P Q U z) (ε : ∀ z, MinusParameters W P Q V z)
    (δ' : ∀ i, PlusParameters (Lax342547.PairedRecipes.flip W) Q P U' i) (ε' : ∀ i, MinusParameters (Lax342547.PairedRecipes.flip W) Q P V' i)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (hA : ∀ z, fullResponse W P Q U V F z (extraFamily W P Q U V z (δ z) (ε z)) (δ z) (ε z) =
      ∑ i, (Lax342547.RecipeResiduals.residual W D L R F i z).comp (LinearMap.proj i))
    (hB : ∀ i, fullResponse (Lax342547.PairedRecipes.flip W) Q P U' V' F.flip i
      (extraFamily (Lax342547.PairedRecipes.flip W) Q P U' V' i (δ' i) (ε' i)) (δ' i) (ε' i) =
      ∑ z, (Lax342547.RecipeResiduals.residual (Lax342547.PairedRecipes.flip W) D L R F.flip z i).comp (LinearMap.proj z)) :
    (∀ i z x, fullContraction (Lax342547.ChannelAssembly.assemble W P Q U V U' V' F δ ε δ' ε')
      (Profile k n b degree) i z x = (D.role + gradient D L R (leftWitness W i z)) x) ∧
    (∀ i z x, fullContraction (Lax342547.ChannelAssembly.assemble W P Q U V U' V' F δ ε δ' ε').flip
      (Profile k n b degree) z i x = (D.role + gradient D L R (rightWitness W i z)) x) := by
  constructor
  · intro i z x
    exact Lax342547.GradientAssembly.corrected_gradients W P Q U V F _ z (δ z) (ε z)
      (fun e i => Lax342547.ChannelAssembly.assembled_plus W P Q U V U' V' F δ ε δ' ε' e i z)
      (fun e i => Lax342547.ChannelAssembly.assembled_minus W P Q U V U' V' F δ ε δ' ε' e i z)
      D L R (hA z) i x
  · intro i z x
    exact Lax342547.GradientAssembly.corrected_gradients (Lax342547.PairedRecipes.flip W) Q P U' V' F.flip _ i (δ' i) (ε' i)
      (fun e z => Lax342547.ChannelAssembly.reciprocal_plus W P Q U V U' V' F δ ε δ' ε' e i z)
      (fun e z => Lax342547.ChannelAssembly.reciprocal_minus W P Q U V U' V' F δ ε δ' ε' e i z)
      D L R (hB i) z x

end Lax342547Proofs.GradientAssembly
