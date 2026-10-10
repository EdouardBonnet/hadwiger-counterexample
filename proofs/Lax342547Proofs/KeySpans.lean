import Lax342547.KeySpans
import Lax342547Proofs.FreshKeys

namespace Lax342547Proofs.KeySpans

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces Lax342547.KeySpans

variable {Base Comp H N : Type} {b degree : ℕ}

/--
---
conclusion: Lax342547.KeySpans.exclusions_exists
---
The existing sparse-label exclusion works for all sets of size at most
R+14, so it also works for the fourteen selected rays at each endpoint.
-/
theorem exclusions_exists [Fintype Base] [Fintype Comp] [Fintype H] {K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ A : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (A i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧ Excludes P A := by
  obtain ⟨A, hcard, h⟩ := FreshKeys.fresh_keys P hK hdegree
  refine ⟨A, hcard, ?_⟩
  intro a L c z hsize hfresh hmem
  exact h a L c z (fun i => (hsize i).trans (by omega)) hfresh hmem

/--
---
conclusion: Lax342547.KeySpans.independent_sum
---
Push the indexed coefficients and base vectors along the injective
selector labels. The resulting finite sets satisfy the sparse exclusion,
so every indexed coefficient is zero.
-/
theorem independent_sum {I : Fin 2 → Type} [∀ i, Fintype (I i)]
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (label : ∀ i, I i → Fin b → Binary) (base : ∀ i, I i → Base → Binary)
    (hlabel : ∀ i, Function.Injective (label i)) (hcard : ∀ i, Fintype.card (I i) ≤ 14)
    (hfresh : ∀ i x, label i x ∉ A i) (a : Comp × Bool) (c : (Σ i, I i) → Binary)
    (h : (∑ x, c x • ray (H := H) label base x) ∈ tableSpace P a) : ∀ x, c x = 0 := by
  classical
  let L : Fin 2 → Finset (Fin b → Binary) := fun i => Finset.univ.image (label i)
  let coeff : Fin 2 → (Fin b → Binary) → Binary :=
    fun i => Function.extend (label i) (fun x => c ⟨i, x⟩) (fun _ => 0)
  let z : Fin 2 → (Fin b → Binary) → Base → Binary :=
    fun i => Function.extend (label i) (base i) (fun _ => 0)
  have hsize (i : Fin 2) : (L i).card ≤ 14 :=
    (Finset.card_image_le).trans (by simpa using hcard i)
  have hdisjoint (i : Fin 2) : Disjoint (L i) (A i) := by
    apply Finset.disjoint_left.mpr
    intro s hs hsA
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hs
    exact hfresh i x hsA
  have he (i : Fin 2) : (∑ s ∈ L i, coeff i s •
      primalEmbedding (H := H) i (point (selectorEval (degree := degree)) s (z i s))) =
      ∑ x : I i, c ⟨i, x⟩ • ray (H := H) label base ⟨i, x⟩ := by
    dsimp only [L]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x _
      simp only [coeff, z, (hlabel i).extend_apply, ray]
    · intro x _ y _ hxy
      exact hlabel i hxy
  have hmem : (∑ i : Fin 2, ∑ s ∈ L i, coeff i s •
      primalEmbedding i (point (selectorEval (degree := degree)) s (z i s))) ∈ tableSpace P a := by
    simp_rw [he]
    simpa only [Fintype.sum_sigma] using h
  have hz := hA a L coeff z hsize hdisjoint hmem
  rintro ⟨i, x⟩
  have hx := hz i (label i x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  simpa only [coeff, (hlabel i).extend_apply] using hx

/--
---
conclusion: Lax342547.KeySpans.span_disjoint
---
Every vector of the selected-ray span is a finite indexed linear
combination. If it also lies in the table, all coefficients vanish by
the indexed independence theorem, and so does the vector.
-/
theorem span_disjoint {I : Fin 2 → Type} [∀ i, Fintype (I i)]
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (label : ∀ i, I i → Fin b → Binary) (base : ∀ i, I i → Base → Binary)
    (hlabel : ∀ i, Function.Injective (label i)) (hcard : ∀ i, Fintype.card (I i) ≤ 14)
    (hfresh : ∀ i x, label i x ∉ A i) (a : Comp × Bool) :
    Disjoint (tableSpace P a) (Submodule.span Binary (Set.range (ray (H := H) label base))) := by
  rw [Submodule.disjoint_def]
  intro v hv hspan
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Binary).mp hspan
  have hz := independent_sum P A hA label base hlabel hcard hfresh a c (hc ▸ hv)
  rw [← hc]
  simp only [hz, zero_smul, Finset.sum_const_zero]

end Lax342547Proofs.KeySpans
