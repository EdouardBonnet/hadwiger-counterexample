import Lax342547Proofs.FlatSelector
import Lax342547Proofs.MomentRecovery

namespace Lax342547Proofs.LabelBlocks

open Lax342547.MomentSpace Lax342547.FlatRank
open Lax342547.SelectorInterpolation
open MomentForm FlatSelector

variable {Base : Type} [Fintype Base] [DecidableEq Base] {b : ℕ}

def monomialClass (c : PointDomain Base b → Binary) (j : ℕ)
    (S : Finset (Fin b)) (hS : S.card ≤ j) (i : Option Base) : QuotientSpace c j :=
  lowClass c j ⟨feature j (⟨S, hS⟩, i), feature_mem _ _⟩

def baseClass (c : PointDomain Base b → Binary) (j : ℕ) (i : Option Base) : QuotientSpace c j :=
  monomialClass c j ∅ (Nat.zero_le _) i

theorem monomialClass_insert (c : PointDomain Base b → Binary) (j : ℕ)
    (M : Fin b → Module.End Binary (QuotientSpace c j))
    (hM : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f))
    (S : Finset (Fin b)) (a : Fin b) (hSa : (insert a S).card ≤ j) (i : Option Base) :
    monomialClass c j (insert a S) hSa i =
      M a (monomialClass c j S ((Finset.card_le_card (Finset.subset_insert _ _)).trans hSa) i) := by
  rw [monomialClass, monomialClass, hM]
  apply congrArg (form c j).ker.mkQ
  apply Subtype.ext
  ext ω
  change monomial (insert a S) ω.1 * baseEval ω.2 i =
    ω.1 a * (monomial S ω.1 * baseEval ω.2 i)
  rw [SelectorInterpolation.monomial_insert, mul_assoc]

theorem projected_monomial (c : PointDomain Base b → Binary) (j : ℕ)
    (M : Fin b → Module.End Binary (QuotientSpace c j))
    (hM : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f))
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j))
    (heigen : ∀ a s, P s * M a = s a • P s)
    (S : Finset (Fin b)) (hS : S.card ≤ j) (i : Option Base) (s : Fin b → Binary) :
    P s (monomialClass c j S hS i) = monomial S s • P s (baseClass c j i) := by
  induction S using Finset.induction_on with
  | empty => simp [baseClass, monomial]
  | @insert a S ha ih =>
    rw [monomialClass_insert c j M hM S a hS i]
    have he (x : QuotientSpace c j) : P s (M a x) = s a • P s x :=
      LinearMap.congr_fun (heigen a s) x
    rw [he, ih ((Finset.card_le_card (Finset.subset_insert _ _)).trans hS),
      SelectorInterpolation.monomial_insert, smul_smul]

def baseTimes (i : Option Base) : ((Fin b → Binary) → Binary) →ₗ[Binary]
    (PointDomain Base b → Binary) where
  toFun f ω := f ω.1 * baseEval ω.2 i
  map_add' f g := by ext ω; exact add_mul _ _ _
  map_smul' c f := by ext ω; exact mul_assoc _ _ _

omit [Fintype Base] [DecidableEq Base] in
theorem baseTimes_mem (j : ℕ) (i : Option Base) {f : (Fin b → Binary) → Binary}
    (hf : f ∈ selectorSpan b j) : baseTimes i f ∈ functions Base b j := by
  induction hf using Submodule.span_induction with
  | mem f hf => obtain ⟨S, hS, rfl⟩ := hf; exact feature_mem j (⟨S, hS⟩, i)
  | zero => simp
  | add f g _ _ hf hg => simpa using (functions Base b j).add_mem hf hg
  | smul c f _ hf => simpa using (functions Base b j).smul_mem c hf

def polynomialClass (c : PointDomain Base b → Binary) (j : ℕ)
    (f : (Fin b → Binary) → Binary) (hf : f ∈ selectorSpan b j) (i : Option Base) :
    QuotientSpace c j := lowClass c j ⟨baseTimes i f, baseTimes_mem j i hf⟩

theorem projected_polynomial (c : PointDomain Base b → Binary) (j : ℕ)
    (M : Fin b → Module.End Binary (QuotientSpace c j))
    (hM : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f))
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j))
    (heigen : ∀ a s, P s * M a = s a • P s)
    (f : (Fin b → Binary) → Binary) (hf : f ∈ selectorSpan b j)
    (i : Option Base) (s : Fin b → Binary) :
    P s (polynomialClass c j f hf i) = f s • P s (baseClass c j i) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    exact projected_monomial c j M hM P heigen S hS i s
  | zero =>
    have he : (⟨baseTimes i 0, baseTimes_mem j i (selectorSpan b j).zero_mem⟩ :
        functions Base b j) = 0 := by
      apply Subtype.ext
      exact map_zero (baseTimes i)
    unfold polynomialClass
    rw [he]
    simp
  | add f g hfm hgm hf hg =>
    have he : polynomialClass c j (f + g) ((selectorSpan b j).add_mem hfm hgm) i =
        polynomialClass c j f hfm i + polynomialClass c j g hgm i := by
      unfold polynomialClass
      rw [← map_add]
      congr 1
      exact Subtype.ext ((baseTimes i).map_add f g)
    rw [he, map_add, hf, hg]
    exact (add_smul _ _ _).symm
  | smul a f hfm hf =>
    have he : polynomialClass c j (a • f) ((selectorSpan b j).smul_mem a hfm) i =
        a • polynomialClass c j f hfm i := by
      unfold polynomialClass
      rw [← map_smul]
      congr 1
      exact Subtype.ext ((baseTimes i).map_smul a f)
    rw [he, map_smul, hf]
    exact smul_smul _ _ _

theorem isolating_polynomialClass (c : PointDomain Base b → Binary) (j : ℕ)
    (M : Fin b → Module.End Binary (QuotientSpace c j))
    (hM : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f))
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j))
    (heigen : ∀ a s, P s * M a = s a • P s) (hsum : ∑ s, P s = 1)
    (hcard : Nat.card {s // P s ≠ 0} ≤ j + 1)
    (s : Fin b → Binary) (hs : P s ≠ 0) :
    ∃ f, ∃ hf : f ∈ selectorSpan b j,
      ∀ i, polynomialClass c j f hf i = P s (baseClass c j i) := by
  classical
  let Active := {s : Fin b → Binary // P s ≠ 0}
  have hc : Fintype.card Active ≤ j + 1 := by simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨f, hf, he⟩ := SelectorInterpolation.exists_separator
    (fun t : Active => t.val) Subtype.val_injective hc (⟨s, hs⟩ : Active)
  refine ⟨f, hf, ?_⟩
  intro i
  have hsumx : polynomialClass c j f hf i = ∑ t, P t (polynomialClass c j f hf i) := by
    simpa using (LinearMap.congr_fun hsum (polynomialClass c j f hf i)).symm
  rw [hsumx]
  simp_rw [projected_polynomial c j M hM P heigen f hf i]
  rw [Finset.sum_eq_single s]
  · have hsval : f s = 1 := by simpa using he (⟨s, hs⟩ : Active)
    rw [hsval, one_smul]
  · intro t _ hts
    by_cases ht : P t = 0
    · simp [ht]
    · have htval : f t = 0 := by
        have hne : (⟨t, ht⟩ : Active) ≠ ⟨s, hs⟩ := fun h => hts (congrArg Subtype.val h)
        simpa only [hne, if_false] using he (⟨t, ht⟩ : Active)
      rw [htval, zero_smul]
  · simp

noncomputable def block (c : PointDomain Base b → Binary) (j : ℕ)
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j)) (s : Fin b → Binary) :
    Matrix (Option Base) (Option Base) Binary :=
  fun i k => quotientPairing (form c j) (form_symm c j) (P s (baseClass c j i)) (P s (baseClass c j k))

theorem block_properties (c : PointDomain Base b → Binary) (j : ℕ)
    (M : Fin b → Module.End Binary (QuotientSpace c j))
    (hM : ∀ a f, M a (lowClass c j f) = (form c j).ker.mkQ (shift j a f))
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j))
    (heigen : ∀ a s, P s * M a = s a • P s) (hsum : ∑ s, P s = 1)
    (hcard : Nat.card {s // P s ≠ 0} ≤ j + 1) (s : Fin b → Binary) :
    Lax342547.BaseMoments.IsBaseMoment (block c j P s) := by
  constructor
  · intro i k
    exact (FlatRank.quotientPairing_symm (form c j) (form_symm c j)).eq _ _
  · intro i
    by_cases hs : P s = 0
    · simp [block, hs]
    · obtain ⟨f, hf, he⟩ := isolating_polynomialClass c j M hM P heigen hsum hcard s hs
      unfold block
      rw [← he i, ← he none]
      change weightedPairing c (baseTimes i f) (baseTimes i f) =
        weightedPairing c (baseTimes none f) (baseTimes i f)
      apply Finset.sum_congr rfl
      intro ω _
      change c ω * (f ω.1 * baseEval ω.2 i) * (f ω.1 * baseEval ω.2 i) =
        c ω * (f ω.1 * 1) * (f ω.1 * baseEval ω.2 i)
      simp only [mul_one, mul_assoc]
      calc
        _ = c ω * ((f ω.1 * f ω.1) * (baseEval ω.2 i * baseEval ω.2 i)) := by ring
        _ = c ω * (f ω.1 * baseEval ω.2 i) := by rw [BaseMoments.binary_mul_self, BaseMoments.binary_mul_self]
        _ = _ := by rw [← mul_assoc (f ω.1), BaseMoments.binary_mul_self]

theorem block_rank_le (c : PointDomain Base b → Binary) (j : ℕ)
    (P : (Fin b → Binary) → Module.End Binary (QuotientSpace c j)) (s : Fin b → Binary) :
    (block c j P s).rank ≤ Module.finrank Binary (LinearMap.range (P s)) := by
  let B := (quotientPairing (form c j) (form_symm c j)).restrict (LinearMap.range (P s))
  let v (i : Option Base) : LinearMap.range (P s) := ⟨P s (baseClass c j i), LinearMap.mem_range_self _ _⟩
  exact GramRank.rank_gram_le B
    ⟨fun x y => (FlatRank.quotientPairing_symm (form c j) (form_symm c j)).eq x y⟩ v

end Lax342547Proofs.LabelBlocks
