import Lax342547.ProfileCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lax342547.SymmetricFactorization

namespace Lax342547Proofs.ProfileCounting

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace

theorem rank_tuple_exponent {E : Type} [Fintype E] (ρ : E → ℕ) (d K : ℕ)
    (hρ : ∑ e, ρ e ≤ K) : ∑ e, (d * ρ e + ρ e * ρ e) ≤ d * K + K * K := by
  have he (e : E) : ρ e ≤ K := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans hρ
  calc
    _ = d * (∑ e, ρ e) + ∑ e, ρ e * ρ e := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ d * K + ∑ e, K * ρ e := Nat.add_le_add
      (Nat.mul_le_mul_left d hρ) (Finset.sum_le_sum fun e _ => Nat.mul_le_mul_right (ρ e) (he e))
    _ ≤ d * K + K * K := by
      rw [← Finset.mul_sum]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left K hρ) _

/--
---
conclusion: Lax342547.ProfileCounting.card_symmetric_profiles
---
Partition profiles by their component ranks. Each rank is at most K.
For a fixed rank tuple, the checked symmetric factorization count gives
at most 2^(d sum(r_e)+sum(r_e²)), bounded by 2^(dK+K²).
-/
theorem card_symmetric_profiles {I E : Type} [Fintype I] [Fintype E] (K : ℕ) :
    Nat.card {x : E → Matrix I I Binary //
      (∀ e, (x e).transpose = x e) ∧ ∑ e, (x e).rank ≤ K} ≤
      (K + 1) ^ Fintype.card E * 2 ^ (Fintype.card I * K + K * K) := by
  classical
  let T := {x : E → Matrix I I Binary // (∀ e, (x e).transpose = x e) ∧ ∑ e, (x e).rank ≤ K}
  let ρ : T → E → Fin (K + 1) := fun x e => ⟨(x.val e).rank,
    Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans x.property.2)⟩
  have hf (q : E → Fin (K + 1)) :
      Fintype.card {x : T // ρ x = q} ≤ 2 ^ (Fintype.card I * K + K * K) := by
    by_cases hq : ∃ x : T, ρ x = q
    · obtain ⟨x₀, hx₀⟩ := hq
      have hsum : ∑ e, (q e).val ≤ K := by
        rw [← hx₀]
        exact x₀.property.2
      let g : {x : T // ρ x = q} → (e : E) →
          {M : Matrix I I Binary // M.transpose = M ∧ M.rank = (q e).val} :=
        fun x e => ⟨x.val.val e, x.val.property.1 e,
          congrArg (fun r : E → Fin (K + 1) => (r e).val) x.property⟩
      have hg : Function.Injective g := by
        intro x y he
        apply Subtype.ext
        apply Subtype.ext
        funext e
        exact congrArg Subtype.val (congrFun he e)
      calc
        _ ≤ Fintype.card ((e : E) →
            {M : Matrix I I Binary // M.transpose = M ∧ M.rank = (q e).val}) :=
          Fintype.card_le_of_injective g hg
        _ = ∏ e, Fintype.card {M : Matrix I I Binary // M.transpose = M ∧ M.rank = (q e).val} :=
          Fintype.card_pi
        _ ≤ ∏ e, 2 ^ (Fintype.card I * (q e).val + (q e).val * (q e).val) := by
          apply Finset.prod_le_prod'
          intro e _
          simpa only [Nat.card_eq_fintype_card] using
            Lax342547.SymmetricFactorization.card_symmetric_rank (I := I) (q e).val
        _ = 2 ^ (∑ e, (Fintype.card I * (q e).val + (q e).val * (q e).val)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (rank_tuple_exponent _ _ _ hsum)
    · have : IsEmpty {x : T // ρ x = q} := ⟨fun x => hq ⟨x.val, x.property⟩⟩
      simp
  have h := Finset.card_le_mul_card_image_of_maps_to
    (f := ρ) (s := Finset.univ) (t := Finset.univ) (by simp)
    (2 ^ (Fintype.card I * K + K * K)) (fun q _ => by
      simpa only [Fintype.card_subtype] using hf q)
  simpa only [Nat.card_eq_fintype_card, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.mul_comm] using h

open Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.TagGeometry

theorem moment_transpose {Label Coord Base : Type} (p : Label → Coord → Binary)
    (A : Set Base) (w : Matrix (Coord × Option Base) (Coord × Option Base) Binary)
    (hw : w ∈ momentSpace p A) : w.transpose = w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, z, _, rfl⟩ := hw
    ext i j
    change point p s z j * point p s z i = point p s z i * point p s z j
    exact mul_comm _ _
  | zero => simp
  | add w v _ _ hw hv => simp [hw, hv]
  | smul c w _ hw => simp [hw]

theorem profile_transpose {k n b degree : ℕ} (x : Profile k n b degree)
    (e : Component (Tag k)) : (x.val e).transpose = x.val e := by
  classical
  obtain ⟨w, hw⟩ := x.property
  rw [← hw]
  change (∑ t ∈ e.val, w.val t).transpose = ∑ t ∈ e.val, w.val t
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact moment_transpose selectorEval (allowedBase k n t) (w.val t) (w.property t trivial)

/--
---
conclusion: Lax342547.ProfileCounting.card_concrete_profiles
---
Every actual cut-profile component is a sum of symmetric point moments.
The underlying component tuple embeds the bounded-rank cut profiles into
the symmetric tuples counted above.
-/
theorem card_concrete_profiles (k n b degree K : ℕ) :
    Nat.card {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} ≤
      (K + 1) ^ Fintype.card (Component (Tag k)) *
        2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K) := by
  classical
  let f : {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} →
      {x : Component (Tag k) → Moment k n b degree //
        (∀ e, (x e).transpose = x e) ∧ ∑ e, (x e).rank ≤ K} :=
    fun x => ⟨x.val.val, profile_transpose x.val, x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have he : x.val.val = y.val.val := by simpa only [f, Subtype.mk.injEq] using h
    exact Subtype.ext (Subtype.ext he)
  calc
    _ ≤ Nat.card {x : Component (Tag k) → Moment k n b degree //
        (∀ e, (x e).transpose = x e) ∧ ∑ e, (x e).rank ≤ K} :=
      Nat.card_le_card_of_injective f hf
    _ ≤ _ := Lax342547.ProfileCounting.card_symmetric_profiles K

end Lax342547Proofs.ProfileCounting
