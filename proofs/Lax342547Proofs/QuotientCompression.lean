import Lax342547.QuotientCompression
import Lax342547.BarredSpaces
import Lax342547.BaseCompression
import Lax342547.ResponseMatrices
import Lax342547.TableSpaces

namespace Lax342547Proofs.QuotientCompression

open Lax342547.QuotientCompression

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.PairedAnnihilators
open Lax342547.TableSpaces Lax342547.ProjectedPins Lax342547.BaseCompression
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.BarredSpaces
open Lax342547.CutProfiles

/--
---
conclusion: Lax342547.QuotientCompression.nominalLift_primal
---
-/
theorem nominalLift_primal {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (i : Fin 2) (v : B → Binary) :
    nominalLift (H := H) f (primalEmbedding i v) = primalEmbedding i (f i v) := by
  ext ⟨j, b | h⟩
  · by_cases hj : j = i
    · subst j
      simp [nominalLift, primalProjection, primalEmbedding]
    · have hz : primalProjection (H := H) j (primalEmbedding i v) = 0 := by
        ext b
        simp [primalProjection, primalEmbedding, hj]
      change f j _ b = _
      rw [hz, map_zero]
      simp [primalEmbedding, hj]
  · simp [nominalLift, primalEmbedding]

/--
---
conclusion: Lax342547.QuotientCompression.nominalLift_fix
---
-/
theorem nominalLift_fix {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (v : Nominal B H)
    (h : ∀ i, f i (primalProjection i v) = primalProjection i v) : nominalLift f v = v := by
  ext ⟨i, b | h⟩
  · exact congrFun (h i) b
  · rfl

/--
---
conclusion: Lax342547.QuotientCompression.nominalLift_sum
---
-/
theorem nominalLift_sum {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (v : Nominal B H) :
    nominalLift f v = ∑ i, (primalEmbedding i (f i (primalProjection i v)) +
      channelEmbedding i (channelProjection i v)) := by
  classical
  ext ⟨i, b | h⟩ <;>
    simp [nominalLift, primalEmbedding, channelEmbedding, channelProjection,
      Finset.sum_apply, eq_comm]

/--
---
conclusion: Lax342547.QuotientCompression.barred_fixed
---
-/
theorem barred_fixed {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool)
    (f : Fin 2 → Vector k n b degree →ₗ[Binary] Vector k n b degree)
    (hfix : ∀ i v, v ∈ projected P i a ⊔ individualKeys W i a.1 → f i v = v) :
    ∀ v ∈ barred W P U a, nominalLift f v = v := by
  intro v hv
  apply Lax342547.QuotientCompression.nominalLift_fix
  intro i
  apply hfix
  exact Lax342547.BarredSpaces.barred_projection W P U a i ⟨v, hv, rfl⟩

/--
---
conclusion: Lax342547.QuotientCompression.quotient_lift_rank
---
-/
theorem quotient_lift_rank {B H : Type} [Fintype B] [Fintype H]
    (D : Submodule Binary (Nominal B H))
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary))
    (hD : D ≤ D.comap (nominalLift f))
    (S U : Fin 2 → Submodule Binary (H → Binary))
    (hcompl : ∀ i, IsCompl (S i) (U i))
    (hprivate : ∀ i, (U i).map (channelEmbedding (B := B) i) ≤ D) :
    Module.finrank Binary (LinearMap.range (D.mapQ D (nominalLift f) hD)) ≤
      ∑ i, (Module.finrank Binary (LinearMap.range (f i)) + Module.finrank Binary (S i)) := by
  classical
  let g : (∀ i, LinearMap.range (f i) × S i) →ₗ[Binary] (Nominal B H ⧸ D) :=
    { toFun := fun w => D.mkQ (∑ i, (primalEmbedding i (w i).1.val + channelEmbedding i (w i).2.val))
      map_add' := by
        intro w v
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
        simp only [Finset.sum_add_distrib, map_add]
        abel
      map_smul' := by
        intro c w
        simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
          ← smul_add, ← Finset.smul_sum, RingHom.id_apply] }
  have hr : LinearMap.range (D.mapQ D (nominalLift f) hD) ≤ LinearMap.range g := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := D.mkQ_surjective x
    have hc : ∀ i, ∃ s ∈ S i, ∃ u ∈ U i, channelProjection i v = s + u := by
      intro i
      have hv : channelProjection (B := B) i v ∈ S i ⊔ U i := by
        rw [(hcompl i).sup_eq_top]
        trivial
      obtain ⟨s, hs, u, hu, he⟩ := Submodule.mem_sup.mp hv
      exact ⟨s, hs, u, hu, he.symm⟩
    choose s hs u hu he using hc
    let w : ∀ i, LinearMap.range (f i) × S i :=
      fun i => ((f i).rangeRestrict (primalProjection i v), ⟨s i, hs i⟩)
    have hp : ∑ i, channelEmbedding (B := B) i (u i) ∈ D := by
      apply Submodule.sum_mem
      intro i _
      exact hprivate i ⟨u i, hu i, rfl⟩
    have hn : nominalLift f v =
        (∑ i, (primalEmbedding i (f i (primalProjection i v)) + channelEmbedding i (s i))) +
        ∑ i, channelEmbedding i (u i) := by
      rw [Lax342547.QuotientCompression.nominalLift_sum]
      simp only [he, map_add, ← add_assoc, Finset.sum_add_distrib]
    refine ⟨w, ?_⟩
    change D.mkQ _ = D.mkQ (nominalLift f v)
    have hz : D.mkQ (∑ i, channelEmbedding (B := B) i (u i)) = 0 :=
      (Submodule.Quotient.mk_eq_zero D).mpr hp
    rw [hn, map_add, hz, add_zero]
    rfl
  exact (Submodule.finrank_mono hr).trans (by
    simpa only [Module.finrank_pi_fintype, Module.finrank_prod] using g.finrank_range_le)

/--
---
conclusion: Lax342547.QuotientCompression.barred_compression
---
-/
theorem barred_compression {k n b degree r K Dblk : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (a : Component (Tag k) × Bool)
    (U : Fin 2 → Submodule Binary (H → Binary))
    (hcompl : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (A : Fin 2 → Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary))
    (hA : ∀ i q, Module.finrank Binary (LinearMap.range (A i q)) ≤ Dblk)
    (hfix : ∀ i v, v ∈ projected P i a ⊔ individualKeys W i a.1 →
      liftBase (blockMap (A i)) v = v) :
    ∃ q : (Nominal (Coordinate k n b degree) H ⧸ barred W P U a) →ₗ[Binary]
        (Nominal (Coordinate k n b degree) H ⧸ barred W P U a),
      (∀ v, q ((barred W P U a).mkQ v) = (barred W P U a).mkQ
        (nominalLift (fun i => liftBase (blockMap (A i))) v)) ∧
      Module.finrank Binary (LinearMap.range q) ≤
        2 * Fintype.card (SelectorCoordinates b degree) *
          (1 + ((2 * k + 1)^2 + 3) * Dblk) + 2 * K := by
  classical
  let D := barred W P U a
  let f : Fin 2 → Vector k n b degree →ₗ[Binary] Vector k n b degree :=
    fun i => liftBase (blockMap (A i))
  have hD : D ≤ D.comap (nominalLift f) := by
    intro v hv
    change nominalLift f v ∈ D
    rw [Lax342547.QuotientCompression.barred_fixed W P U a f hfix v hv]
    exact hv
  refine ⟨D.mapQ D (nominalLift f) hD, fun v => rfl, ?_⟩
  have hprivate : ∀ i, (U i).map (channelEmbedding (B := Coordinate k n b degree) i) ≤ D := by
    intro i
    exact (le_iSup (fun j => (U j).map (channelEmbedding j)) i).trans le_sup_right
  have hr := Lax342547.QuotientCompression.quotient_lift_rank D f hD (fun i => protectedChannel P i a) U hcompl hprivate
  have hbound : ∀ i, Module.finrank Binary (LinearMap.range (f i)) +
      Module.finrank Binary (protectedChannel P i a) ≤
        Fintype.card (SelectorCoordinates b degree) * (1 + ((2 * k + 1)^2 + 3) * Dblk) + K := by
    intro i
    exact Nat.add_le_add (Lax342547.BaseCompression.concrete_compression_rank (A i) (hA i))
      (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
        (Lax342547.TableSpaces.protected_rank P i)).trans hK)
  have hh := hr.trans (Finset.sum_le_sum (fun i _ => hbound i))
  simpa [mul_add, mul_assoc] using hh

/--
---
conclusion: Lax342547.QuotientCompression.compressed_bilinear_rank
---
-/
theorem compressed_bilinear_rank {A B : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup B] [Module Binary B] [FiniteDimensional Binary A]
    (β : A →ₗ[Binary] B →ₗ[Binary] Binary) (q : A →ₗ[Binary] A) (p : B →ₗ[Binary] B) :
    Module.finrank Binary (LinearMap.range (β.compl₁₂ q p)) ≤
      Module.finrank Binary (LinearMap.range q) := by
  change Module.finrank Binary (LinearMap.range ((β.compl₂ p).comp q)) ≤ _
  exact Lax342547.ResponseMatrices.comp_right_rank _ _

/--
---
conclusion: Lax342547.QuotientCompression.pure_compressed
---
-/
theorem pure_compressed {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H))
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary)
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary))
    (qD : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ D))
    (qE : (Nominal B H ⧸ E) →ₗ[Binary] (Nominal B H ⧸ E))
    (hD : ∀ v, qD (D.mkQ v) = D.mkQ (nominalLift f v))
    (hE : ∀ v, qE (E.mkQ v) = E.mkQ (nominalLift f v))
    (x : Fin 2 → Matrix B B Binary) :
    pureResponse D E (β.compl₁₂ qD qE) x =
      pureResponse D E β (fun i => tensorMap (f i) (x i)) := by
  classical
  let C : Fin 2 → LinearMap.BilinForm Binary (B → Binary) :=
    fun i => β.compl₁₂ (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i))
  have hb (i : Fin 2) : (β.compl₁₂ qD qE).compl₁₂
      (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i)) =
      (C i).compl₁₂ (f i) (f i) := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change β (qD (D.mkQ (primalEmbedding i v))) (qE (E.mkQ (primalEmbedding i w))) = _
    rw [hD, hE, Lax342547.QuotientCompression.nominalLift_primal, Lax342547.QuotientCompression.nominalLift_primal]
    rfl
  simp only [pureResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb]
  have hm : LinearMap.BilinForm.toMatrix' ((C i).compl₁₂ (f i) (f i)) =
      (LinearMap.toMatrix' (f i)).transpose * LinearMap.BilinForm.toMatrix' (C i) *
        LinearMap.toMatrix' (f i) := by
    change LinearMap.BilinForm.toMatrix' (LinearMap.BilinForm.comp (C i) (f i) (f i)) = _
    rw [LinearMap.BilinForm.toMatrix'_comp]
  rw [hm]
  exact (Lax342547.BaseCompression.matrixPair_tensorMap (f i)
    (LinearMap.BilinForm.toMatrix' (C i)) (x i)).symm

end Lax342547Proofs.QuotientCompression
