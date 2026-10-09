import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Lax342547Proofs.LinearExtension

open LinearMap

variable {K U V V' W : Type*} [Field K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']
  [AddCommGroup W] [Module K W]

theorem extend_injections [FiniteDimensional K V] [FiniteDimensional K V']
    (hdim : Module.finrank K V = Module.finrank K V')
    (A : U →ₗ[K] V) (A' : U →ₗ[K] V')
    (hA : Function.Injective A) (hA' : Function.Injective A') :
    ∃ e : V ≃ₗ[K] V', ∀ u, e (A u) = A' u := by
  let e₀ := LinearEquiv.ofFinrankEq (R := K) V V' hdim
  let B := e₀.symm.toLinearMap.comp A'
  have hB : Function.Injective B := e₀.symm.injective.comp hA'
  let f := (LinearEquiv.ofInjective A hA).symm.trans (LinearEquiv.ofInjective B hB)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g.trans e₀, fun u => ?_⟩
  have h := hg (LinearEquiv.ofInjective A hA u)
  have h' : B u = g (A u) := by simpa [f] using h
  change e₀ (g (A u)) = A' u
  rw [← h']
  exact e₀.apply_symm_apply (A' u)

theorem split_surjection (p : V →ₗ[K] W) (hp : Function.Surjective p) :
    ∃ e : V ≃ₗ[K] (LinearMap.ker p × W), ∀ v, (e v).2 = p v := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (range_eq_top.mpr hp)
  have hs' (w : W) : p (s w) = w := DFunLike.congr_fun hs w
  let f : (LinearMap.ker p × W) →ₗ[K] V := (LinearMap.ker p).subtype.coprod s
  have hf (x : LinearMap.ker p × W) : p (f x) = x.2 := by
    simp [f, hs']
  have hinj : Function.Injective f := by
    intro x y h
    have h₂ : x.2 = y.2 := by simpa only [hf] using congrArg p h
    apply Prod.ext _ h₂
    apply Subtype.ext
    simpa [f, h₂] using h
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨(⟨v - s (p v), ?_⟩, p v), ?_⟩
    · simp [LinearMap.mem_ker, hs']
    · simp [f]
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e.symm, fun v => ?_⟩
  have h := hf (e.symm v)
  simpa only [show f (e.symm v) = v from e.apply_symm_apply v] using h.symm

theorem factor_through (T : U →ₗ[K] W) (d : U →ₗ[K] V)
    (h : LinearMap.ker T ≤ LinearMap.ker d) :
    ∃ b : W →ₗ[K] V, ∀ u, b (T u) = d u := by
  let c := (LinearMap.ker T).liftQ d h
  let f := c.comp T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨b, hb⟩ := f.exists_extend
  refine ⟨b, fun u => ?_⟩
  have he := DFunLike.congr_fun hb (T.rangeRestrict u)
  change b (T u) = c (T.quotKerEquivRange.symm ⟨T u, T.mem_range_self u⟩) at he
  rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
  exact he

noncomputable def shear (e : V ≃ₗ[K] V') (b : W →ₗ[K] V') :
    (V × W) ≃ₗ[K] (V' × W) where
  toFun x := (e x.1 + b x.2, x.2)
  invFun y := (e.symm (y.1 - b y.2), y.2)
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by ext <;> simp; abel
  map_smul' c x := by ext <;> simp [smul_add]

set_option backward.isDefEq.respectTransparency false in
theorem commuting_extension [FiniteDimensional K V] [FiniteDimensional K V']
    (hdim : Module.finrank K V = Module.finrank K V')
    (A : U →ₗ[K] V) (A' : U →ₗ[K] V') (p : V →ₗ[K] W) (p' : V' →ₗ[K] W)
    (hA : Function.Injective A) (hA' : Function.Injective A')
    (hp : Function.Surjective p) (hp' : Function.Surjective p')
    (hcomm : p.comp A = p'.comp A') :
    ∃ e : V ≃ₗ[K] V', (∀ u, e (A u) = A' u) ∧ ∀ v, p' (e v) = p v := by
  obtain ⟨E, hE⟩ := split_surjection p hp
  obtain ⟨E', hE'⟩ := split_surjection p' hp'
  let T := p.comp A
  let a := (LinearMap.fst K (LinearMap.ker p) W).comp (E.toLinearMap.comp A)
  let a' := (LinearMap.fst K (LinearMap.ker p') W).comp (E'.toLinearMap.comp A')
  have hT (u : U) : p' (A' u) = T u := (DFunLike.congr_fun hcomm u).symm
  have ha : Function.Injective (a.comp (LinearMap.ker T).subtype) := by
    intro x y h
    apply Subtype.ext
    apply hA
    apply E.injective
    apply Prod.ext h
    change (E (A x)).2 = (E (A y)).2
    rw [hE, hE]
    exact x.property.trans y.property.symm
  have ha' : Function.Injective (a'.comp (LinearMap.ker T).subtype) := by
    intro x y h
    apply Subtype.ext
    apply hA'
    apply E'.injective
    apply Prod.ext h
    change (E' (A' x)).2 = (E' (A' y)).2
    rw [hE', hE', hT, hT]
    exact x.property.trans y.property.symm
  have hker : Module.finrank K (LinearMap.ker p) =
      Module.finrank K (LinearMap.ker p') := by
    have h := p.finrank_range_add_finrank_ker
    have h' := p'.finrank_range_add_finrank_ker
    rw [range_eq_top.mpr hp, finrank_top] at h
    rw [range_eq_top.mpr hp', finrank_top] at h'
    omega
  obtain ⟨e, he⟩ := extend_injections hker
    (a.comp (LinearMap.ker T).subtype) (a'.comp (LinearMap.ker T).subtype) ha ha'
  let d := a' - e.toLinearMap.comp a
  have hd : LinearMap.ker T ≤ LinearMap.ker d := by
    intro u hu
    change a' u - e (a u) = 0
    exact sub_eq_zero.mpr (he ⟨u, hu⟩).symm
  obtain ⟨b, hb⟩ := factor_through T d hd
  let L := E.trans ((shear e b).trans E'.symm)
  refine ⟨L, ?_, ?_⟩
  · intro u
    apply E'.injective
    change E' (E'.symm ((shear e b) (E (A u)))) = E' (A' u)
    rw [E'.apply_symm_apply]
    apply Prod.ext
    · change e (a u) + b ((E (A u)).2) = a' u
      rw [hE]
      change e (a u) + b (T u) = a' u
      rw [hb]
      change e (a u) + (a' u - e (a u)) = a' u
      abel
    · change (E (A u)).2 = (E' (A' u)).2
      rw [hE, hE', hT]
      rfl
  · intro v
    rw [← hE']
    change (E' (E'.symm ((shear e b) (E v)))).2 = p v
    rw [E'.apply_symm_apply]
    exact hE v

end Lax342547Proofs.LinearExtension
