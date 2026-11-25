import Lax793645Proofs.Simplifications.QuadraticOneVector
import Lax793645Proofs.Simplifications.QuadraticColumnCounts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {B H : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup H] [Module QField H]

private lemma binary_sup_decompose (S : Submodule QField B) (x z : B)
    (hz : z∈S⊔Submodule.span QField {x}) :
    ∃ s : S,z=(s:B) ∨ z=(s:B)+x := by
  obtain ⟨s,hs,t,ht,hst⟩ := Submodule.mem_sup.mp hz
  obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp ht
  rcases ((by decide : ∀ r : QField,r=0∨r=1) r) with rfl|rfl
  · exact ⟨⟨s,hs⟩,Or.inl (by simpa using hst.symm)⟩
  · exact ⟨⟨s,hs⟩,Or.inr (by simpa using hst.symm)⟩

/-- A new column with the required pairings extends the partial frame linearly. -/
theorem quadratic_extend_column
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (S : Submodule QField B) (g₀ : S →ₗ[QField] H) (hinj : Function.Injective g₀)
    (hq : ∀ s : S, q (g₀ s) = Q s) (x : B) (hx : x ∉ S)
    (y : H) (hy : y ∉ g₀.range) (hyq : q y = Q x)
    (hpair : ∀ s : S, q.polarBilin (g₀ s) y = Q.polarBilin s x) :
    ∃ g : (S⊔Submodule.span QField {x} : Submodule QField B)→ₗ[QField] H,
      Function.Injective g ∧ (∀ z,q (g z)=Q z) ∧
      ∀ s : S,g ⟨s,Submodule.mem_sup_left s.property⟩=g₀ s := by
  classical
  obtain ⟨f,hf,hfx⟩ := g₀.exists_extend_of_notMem hx y
  have hfs (s : S) : f s=g₀ s := LinearMap.congr_fun hf s
  let T := S⊔Submodule.span QField {x}
  let g : T→ₗ[QField] H := f.comp T.subtype
  have hg (z : T) : g z=f z := rfl
  have hinjg : Function.Injective g := by
    apply (LinearMap.ker_eq_bot).mp
    ext z
    simp only [LinearMap.mem_ker,Submodule.mem_bot]
    constructor
    · intro hz
      obtain ⟨s,hs|hs⟩ := binary_sup_decompose S x z z.property
      · have hzero : g₀ s=0 := by simpa only [hg,hs,hfs] using hz
        have hs0 : s=0 := hinj (hzero.trans (map_zero g₀).symm)
        apply Subtype.ext
        simp only [hs,hs0,ZeroMemClass.coe_zero]
      · have hy0 : g₀ s+y=0 := by simpa only [hg,hs,map_add,hfs,hfx] using hz
        have hys : y=g₀ s := by
          have hh : g₀ s+g₀ s=0 := ZModModule.add_self _
          exact add_left_cancel (hy0.trans hh.symm)
        exact (hy ⟨s,hys.symm⟩).elim
    · rintro rfl
      exact map_zero g
  refine ⟨g,hinjg,?_,?_⟩
  · intro z
    change q (f (z:B))=Q (z:B)
    obtain ⟨s,hs|hs⟩ := binary_sup_decompose S x z z.property
    · simpa only [hs,hfs] using hq s
    · simp only [hs,map_add,hfs,hfx]
      rw [QuadraticMap.map_add q,QuadraticMap.map_add Q]
      rw [hq,hyq,←QuadraticMap.polarBilin_apply_apply,
        ←QuadraticMap.polarBilin_apply_apply,hpair]
  · intro s
    exact hfs s

/-- Enlarge a partial injective quadratic isometry by one domain direction. -/
theorem quadratic_embedding_step [FiniteDimensional QField B] [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate) (S : Submodule QField B)
    (g₀ : S→ₗ[QField] H) (hinj : Function.Injective g₀)
    (hq : ∀ s : S,q (g₀ s)=Q s) (x : B) (hx : x∉S)
    (hroom : 2*Module.finrank QField S+4≤Module.finrank QField H) :
    ∃ g : (S⊔Submodule.span QField {x} : Submodule QField B)→ₗ[QField] H,
      Function.Injective g ∧ (∀ z,q (g z)=Q z) ∧
      ∀ s : S,g ⟨s,Submodule.mem_sup_left s.property⟩=g₀ s := by
  classical
  let e := LinearEquiv.ofInjective g₀ hinj
  let b : g₀.range→ₗ[QField] QField :=
    ((Q.polarBilin x).comp S.subtype).comp e.symm.toLinearMap
  have hd : Module.finrank QField g₀.range=Module.finrank QField S := e.finrank_eq.symm
  let _ : Finite H := Module.finite_of_finite QField
  let _ : Fintype H := Fintype.ofFinite H
  obtain ⟨y,hy,hyq,hyp⟩ := quadratic_column_exists q hnd g₀.range b (Q x)
    (show 2*Module.finrank QField g₀.range+4≤Module.finrank QField H by omega)
  have hpair (s : S) : q.polarBilin (g₀ s) y=Q.polarBilin s x := by
    have hh := hyp (e s)
    change q.polarBilin (g₀ s) y=Q.polarBilin x (e.symm (e s)) at hh
    simpa only [LinearEquiv.symm_apply_apply,QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm] using hh
  exact quadratic_extend_column Q q S g₀ hinj hq x hx y hy hyq hpair

/-- Iterating independent column extensions completes a frame. -/
theorem quadratic_extend_by_steps [FiniteDimensional QField B]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (step : ∀ (S : Submodule QField B) (g₀ : S →ₗ[QField] H),
      Function.Injective g₀ → (∀ s : S, q (g₀ s) = Q s) →
      ∀ x : B, x ∉ S → ∃ g : (S ⊔ Submodule.span QField {x} : Submodule QField B) →ₗ[QField] H,
        Function.Injective g ∧ (∀ z, q (g z) = Q z) ∧
        ∀ s : S, g ⟨s,Submodule.mem_sup_left s.property⟩ = g₀ s)
    (S : Submodule QField B) (g₀ : S→ₗ[QField] H)
    (hinj : Function.Injective g₀) (hq : ∀ s : S,q (g₀ s)=Q s) :
    ∃ g : B→ₗ[QField] H,Function.Injective g ∧ (∀ b,q (g b)=Q b) ∧
      ∀ s : S,g s=g₀ s := by
  classical
  have extend : ∀ k : ℕ,∀ (S : Submodule QField B),
      Module.finrank QField B-Module.finrank QField S=k →
      ∀ (g₀ : S→ₗ[QField] H),Function.Injective g₀ →
      (∀ s : S,q (g₀ s)=Q s) →
      ∃ g : B→ₗ[QField] H,Function.Injective g ∧ (∀ b,q (g b)=Q b) ∧
        ∀ s : S,g s=g₀ s := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hk g₀ hinj hq
      by_cases hS : S=⊤
      · subst S
        let g : B→ₗ[QField] H := g₀.comp
          (Submodule.topEquiv : (⊤ : Submodule QField B)≃ₗ[QField] B).symm.toLinearMap
        refine ⟨g,?_,?_,?_⟩
        · intro a b hab
          exact congrArg Subtype.val (hinj hab)
        · intro b
          exact hq ⟨b,Submodule.mem_top⟩
        · intro s
          rfl
      · have hx : ∃ x : B,x∉S := by
          by_contra hh
          push Not at hh
          exact hS (Submodule.eq_top_iff'.mpr hh)
        obtain ⟨x,hx⟩ := hx
        obtain ⟨f,hfi,hfq,hfS⟩ := step S g₀ hinj hq x hx
        let T := S⊔Submodule.span QField {x}
        have hST : S<T := lt_of_le_of_ne le_sup_left (by
          intro he
          apply hx
          rw [he]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
        have hdT := Submodule.finrank_lt_finrank_of_lt hST
        have hdB := Submodule.finrank_le T
        have hkT : Module.finrank QField B-Module.finrank QField T<k := by omega
        obtain ⟨g,hgi,hgq,hgT⟩ := ih _ hkT T rfl f hfi hfq
        refine ⟨g,hgi,hgq,?_⟩
        intro s
        exact (hgT ⟨s,Submodule.mem_sup_left s.property⟩).trans (hfS s)
  exact extend _ S rfl g₀ hinj hq

/-- Every partial injective isometry into a sufficiently large binary
quadratic space with nondegenerate polar form extends to the whole domain.
The domain form is allowed to be degenerate. -/
theorem quadratic_embedding_extension [FiniteDimensional QField B]
    [FiniteDimensional QField H]
    (Q : QuadraticForm QField B) (q : QuadraticForm QField H)
    (hnd : q.polarBilin.Nondegenerate)
    (hroom : 2*Module.finrank QField B+2≤Module.finrank QField H)
    (S : Submodule QField B) (g₀ : S→ₗ[QField] H)
    (hinj : Function.Injective g₀) (hq : ∀ s : S,q (g₀ s)=Q s) :
    ∃ g : B→ₗ[QField] H,Function.Injective g ∧ (∀ b,q (g b)=Q b) ∧
      ∀ s : S,g s=g₀ s := by
  apply quadratic_extend_by_steps Q q _ S g₀ hinj hq
  intro T j hj hform x hx
  have hT : T ≠ ⊤ := fun he => hx (he ▸ Submodule.mem_top)
  have hd := Submodule.finrank_lt hT
  exact quadratic_embedding_step Q q hnd T j hj hform x hx (by omega)

end
end Lax793645Proofs.Simplifications
