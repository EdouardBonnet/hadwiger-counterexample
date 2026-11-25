import Lax793645Proofs.Simplifications.OneScalarRecipes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneGradientRank (p : Shape) : ℕ :=
  2*(15*p.r+14*p.J*Fintype.card (Comp p.g))

def oneRealizationRoom (p : Shape) (K t : ℕ) : Prop :=
  let f:=2*(K+t)
  oneGradientRank p+(f+K)+jointCompressionRank p f (2*f+(f+K))+5*K+6*f+2≤p.h

/-- The complete scalar-to-table step for the one-frame construction.
The effective spaces are the actual closed primal pins. Key freezing,
the explicit gradients, obstruction tests and both quadratic extensions
are constructed inside the proof. -/
theorem one_scalar_realization
    (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (hg : Odd p.g) (hv : v.legal t) (hw : w.legal t)
    (hbv : v.bounded w.obj) (hbw : w.bounded v.obj)
    (x y : OneUnit p n N)
    (hx : ∀ i,oneFrameLaw m (x i)) (hy : ∀ i,oneFrameLaw m (y i))
    (a b : ImagePlan (Comp p.g) (OneColumn p n)) (K : ℕ)
    (ha : (onePinClosure p n).close a=a) (hb : (onePinClosure p n).close b=b)
    (hKa : ∀ e,dim (a e)≤K) (hKb : ∀ e,dim (b e)≤K)
    (hprotA : OneProtectedVolley v t (oneEndpointPrimalPins a) (4*(K+Fintype.card I)))
    (hprotB : OneProtectedVolley w t (oneEndpointPrimalPins b) (4*(K+Fintype.card I)))
    (hsafeA : onePinSafe (oneEndpointPrimalPins a) (oneChannelPins b) x y)
    (hsafeB : onePinSafe (oneEndpointPrimalPins b) (oneChannelPins a) y x)
    (hkeys : oneVolleyKeys v t x=oneVolleyKeys w t y)
    (hrecipeA : OneScalarRecipe v w.obj t m x y (oneEndpointPrimalPins a))
    (hrecipeB : OneScalarRecipe w v.obj t m y x (oneEndpointPrimalPins b))
    (hatA : oneAttackGrad v w t m y) (hatB : oneAttackGrad w v t m x)
    (hroom : oneRealizationRoom p K (Fintype.card I)) :
    ∃ Q : OneCross p n,OneRealized v w t m Q ∧
      imageRowAgree (a⊔oneKeyPlan v t) Q (oneCrossMatrix x y) ∧
      imageRowAgree (b⊔oneKeyPlan w t) (fun e=>(Q e)ᵀ) (oneCrossMatrix y x) := by
  obtain ⟨MA,hMA,hgradA⟩:=one_gradient_targets v w.obj t m hg hv hbv hrecipeA.summ
  obtain ⟨MB,hMB,hgradB⟩:=one_gradient_targets w v.obj t m hg hw hbw hrecipeB.summ
  apply one_build_selected_table v w t hv hw m x y (a⊔oneKeyPlan v t) (b⊔oneKeyPlan w t)
    (oneEndpointPrimalPins a) (oneEndpointPrimalPins b) (4*(K+Fintype.card I))
    hprotA hprotB (one_frozen_primal_pins v t a ha) (one_frozen_primal_pins w t b hb)
    (by simpa only [one_frozen_channel_pins] using hsafeA)
    (by simpa only [one_frozen_channel_pins] using hsafeB)
    MA MB (2*(K+Fintype.card I)) K (oneGradientRank p) ?_ ?_ ?_ ?_ hMA hMB
    (fun i j z _=>hgradA i j z) (fun j i z _=>hgradB j i z) ?_ ?_ ?_ ?_ hroom
  · rw [one_frozen_primal_pins v t a ha]
    exact one_selected_primal_dimension v t _ K
      (fun i e=>(one_endpoint_primal_pin_dimension a i e).trans (hKa e))
  · rw [one_frozen_primal_pins w t b hb]
    exact one_selected_primal_dimension w t _ K
      (fun i e=>(one_endpoint_primal_pin_dimension b i e).trans (hKb e))
  · rw [one_frozen_channel_pins]
    exact fun i e=>(one_channel_pin_dimension a i e).trans (hKa e)
  · rw [one_frozen_channel_pins]
    exact fun i e=>(one_channel_pin_dimension b i e).trans (hKb e)
  · exact one_recipe_atoms v w t m x y hv hy hkeys hatA MA hgradA
  · simp_rw [one_right_channels_reciprocal]
    exact one_recipe_atoms w v t m y x hw hx hkeys.symm hatB MB hgradB
  · exact one_recipe_effective v w.obj t m x y _ hrecipeA MA hgradA
  · simp_rw [one_right_channels_reciprocal]
    exact one_recipe_effective w v.obj t m y x _ hrecipeB MB hgradB

end
end Lax793645Proofs.Simplifications
