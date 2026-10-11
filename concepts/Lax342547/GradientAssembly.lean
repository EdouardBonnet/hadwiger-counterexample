import Lax342547.ChannelAssembly

/-!
---
title: All four whole-space gradient equations from assembled channel changes
type: lemma
---
Expanding the actual nonlinear contractions identifies their changes with the pure-plus-derivative response. The actual recipe residual cancels the baseline contraction. Opposite-endpoint and reciprocal-role assembly then gives all four gradient equations on the entire profile space.
-/

namespace Lax342547.GradientAssembly

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.BarredSpaces Lax342547.PairedKeys
open Lax342547.ResidualRealization Lax342547.NonlinearChannels

axiom contraction_expansion {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
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
        fullResponse W P Q U V F z (extraFamily W P Q U V z δ ε) δ ε x

axiom corrected_gradients {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
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
      (D.role + gradient D L R (leftWitness W i z)) x

axiom simultaneous_gradients {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
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
      (Profile k n b degree) z i x = (D.role + gradient D L R (rightWitness W i z)) x)

end Lax342547.GradientAssembly
