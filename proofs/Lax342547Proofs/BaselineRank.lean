import Lax342547.BaselineRank
import Lax342547.FrozenBaselines
import Lax342547.PrimalRetractions

namespace Lax342547Proofs.BaselineRank

open Lax342547.MomentSpace Lax342547.FrozenBaselines Lax342547.BaselineRank

variable {V W C : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W] [AddCommGroup C] [Module Binary C]

/--
---
conclusion: Lax342547.BaselineRank.channel_rank
---
For an opposite channel, its frozen projection is a pin. The baseline
evaluation is the sum of a function of the retracted primal input and
the actual input's pairing with that pin. Factor through the product of
the primal retraction's range and the opposite pin dual, then count its
dimension.
-/
theorem channel_rank [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' : Submodule Binary W)
    (hD : D ≤ J) (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (p : V →ₗ[Binary] V) (hfix : ∀ v ∈ J ⊔ Keys, p v = v)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (q : C →ₗ[Binary] J') :
    Module.finrank Binary (LinearMap.range
      ((baseline (retracted S hD p hfix) S' A T).compl₁₂ U.subtype (J'.subtype.comp q))) ≤
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) + Module.finrank Binary D' := by
  let rU := p.comp U.subtype
  let ch := J'.subtype.comp q
  let first : V →ₗ[Binary] C →ₗ[Binary] Binary :=
    A.compl₁₂ S.frozen ch - A.compl₁₂ S.frozen (S'.frozen.comp ch) +
      T.compl₁₂ S.table (S'.table.comp ch)
  let dch : C →ₗ[Binary] D' :=
    (S'.frozen.comp ch).codRestrict D' (fun x => S'.frozen_table (q x))
  let input : U →ₗ[Binary] (LinearMap.range rU × Module.Dual Binary D') :=
    rU.rangeRestrict.prod (A.compl₁₂ U.subtype D'.subtype)
  let output : (LinearMap.range rU × Module.Dual Binary D') →ₗ[Binary]
      Module.Dual Binary C := (first.comp (LinearMap.range rU).subtype).coprod dch.dualMap
  have hfactor : (baseline (retracted S hD p hfix) S' A T).compl₁₂ U.subtype ch =
      output.comp input := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro x
    change A (S.frozen (p v.val)) (ch x) + A v.val (S'.frozen (ch x)) -
        A (S.frozen (p v.val)) (S'.frozen (ch x)) + T (S.table (p v.val)) (S'.table (ch x)) =
      (A (S.frozen (p v.val)) (ch x) - A (S.frozen (p v.val)) (S'.frozen (ch x)) +
        T (S.table (p v.val)) (S'.table (ch x))) + A v.val (S'.frozen (ch x))
    abel
  rw [hfactor]
  calc
    _ ≤ Module.finrank Binary (LinearMap.range output) :=
      Submodule.finrank_mono (LinearMap.range_comp_le_range input output)
    _ ≤ Module.finrank Binary (LinearMap.range rU × Module.Dual Binary D') := output.finrank_range_le
    _ = _ := by rw [Module.finrank_prod, Subspace.dual_finrank_eq]

/--
---
conclusion: Lax342547.BaselineRank.bounded_baseline
---
Choose the independent frozen/table splittings, and precompose both
with primal-preserving retractions onto table plus keys. This keeps
all baseline agreements while bounding its primal channel rank by the
table-primal dimension, number of key directions, and opposite pin rank.
-/
theorem bounded_baseline [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' U' : Submodule Binary W)
    (hD : D ≤ J) (hD' : D' ≤ J') (hKeys : Disjoint J Keys) (hKeys' : Disjoint J' Keys')
    (hspan : J ⊔ U = ⊤) (hKeyPrimal : Keys ≤ U)
    (hspan' : J' ⊔ U' = ⊤) (hKeyPrimal' : Keys' ≤ U')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (h : Compatible J D J' D' A T) :
    ∃ B : V →ₗ[Binary] W →ₗ[Binary] Binary,
      ExtendsFrozen D Keys D' Keys' A B ∧ (∀ v : J, ∀ w : J', B v.val w.val = T v w) ∧
      (∀ q : C →ₗ[Binary] J',
        Module.finrank Binary (LinearMap.range (B.compl₁₂ U.subtype (J'.subtype.comp q))) ≤
          Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys + Module.finrank Binary D') ∧
      ∀ q : C →ₗ[Binary] J,
        Module.finrank Binary (LinearMap.range (B.flip.compl₁₂ U'.subtype (J.subtype.comp q))) ≤
          Module.finrank Binary ↥(J' ⊓ U') + Module.finrank Binary Keys' + Module.finrank Binary D := by
  obtain ⟨S⟩ := Lax342547.FrozenBaselines.splitting_exists J D Keys hD hKeys
  obtain ⟨S'⟩ := Lax342547.FrozenBaselines.splitting_exists J' D' Keys' hD' hKeys'
  obtain ⟨p, _hp, hfix, _hU, hrank⟩ := Lax342547.PrimalRetractions.bounded_retraction J Keys U hspan hKeyPrimal
  obtain ⟨p', _hp', hfix', _hU', hrank'⟩ := Lax342547.PrimalRetractions.bounded_retraction J' Keys' U' hspan' hKeyPrimal'
  let RS := retracted S hD p hfix
  let RS' := retracted S' hD' p' hfix'
  let B := baseline RS RS' A T
  have hB := Lax342547.FrozenBaselines.baseline_properties J D Keys J' D' Keys' hD hD'
    RS RS' A T h
  refine ⟨B, hB.1, hB.2, ?_, ?_⟩
  · intro q
    exact (Lax342547.BaselineRank.channel_rank J D Keys U J' D' Keys' hD S RS' p hfix A T q).trans
      (Nat.add_le_add_right hrank _)
  · intro q
    have hflip : B.flip = baseline RS' RS A.flip T.flip := by
      apply LinearMap.ext
      intro w
      apply LinearMap.ext
      intro v
      change A (RS.frozen v) w + A v (RS'.frozen w) - A (RS.frozen v) (RS'.frozen w) +
          T (RS.table v) (RS'.table w) =
        A v (RS'.frozen w) + A (RS.frozen v) w - A (RS.frozen v) (RS'.frozen w) +
          T (RS.table v) (RS'.table w)
      abel
    rw [hflip]
    exact (Lax342547.BaselineRank.channel_rank J' D' Keys' U' J D Keys hD' S' RS p' hfix' A.flip T.flip q).trans
      (Nat.add_le_add_right hrank' _)

end Lax342547Proofs.BaselineRank
