import Lax342547.RawBaselines
import Lax342547Proofs.PairedKeys
import Lax342547Proofs.NominalBaselines

namespace Lax342547Proofs.RawBaselines

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.PairedKeys
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.ReferencePins
open Lax342547.NominalPrimal Lax342547.FrozenBaselines Lax342547.KeySpans Lax342547.RawBaselines

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

/--
---
conclusion: Lax342547.RawBaselines.raw_baselines
---
The sparse exclusions imply independence of the actual incident key
spans. Their dimensions are at most twenty-eight. Admissibility is
exactly the compatibility needed by the nominal baseline theorem.
Apply it to both cross orientations and assemble the two full forms;
each has both reciprocal rank bounds and retains every frozen entry.
-/
theorem raw_baselines (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A) (hB : Excludes Q B)
    (hfresh : FreshAgainst W A B) (K : ℕ) (hP : P.rank ≤ K) (hQ : Q.rank ≤ K)
    (oA oB : Unit (H := H) (N := N) (E := E)) (T : Table P Q)
    (hadmissible : Admissible T observation observation oA oB) :
    ∃ F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H,
      Extends F T ∧ Frozen F W P Q oA oB ∧ Bounded F K := by
  have hfreshKeys := PairedKeys.fresh_spans W P Q A B hA hB hfresh
  have hforward (e : Component (Tag k)) := NominalBaselines.nominal_baseline
    P Q (e, true) (e, false) (keys W e) (keys (flip W) e) K hP hQ
    (PairedKeys.key_bounds W e).1 (PairedKeys.key_bounds (flip W) e).1
    (PairedKeys.key_bounds W e).2 (PairedKeys.key_bounds (flip W) e).2
    (hfreshKeys.1 (e, true)) (hfreshKeys.2 (e, false))
    ((rawForms oA oB).forward e) (T.forward e) (hadmissible.1 e)
  have hreverse (e : Component (Tag k)) := NominalBaselines.nominal_baseline
    Q P (e, true) (e, false) (keys (flip W) e) (keys W e) K hQ hP
    (PairedKeys.key_bounds (flip W) e).1 (PairedKeys.key_bounds W e).1
    (PairedKeys.key_bounds (flip W) e).2 (PairedKeys.key_bounds W e).2
    (hfreshKeys.2 (e, true)) (hfreshKeys.1 (e, false))
    ((rawForms oA oB).reverse e) (T.reverse e) (hadmissible.2 e)
  choose F hFF hFT hFR using hforward
  choose G hGF hGT hGR using hreverse
  exact ⟨⟨F, G⟩, ⟨hFT, hGT⟩, fun e => ⟨hFF e, hGF e⟩,
    fun e z => ⟨(hFR e z).1, (hFR e z).2, (hGR e z).1, (hGR e z).2⟩⟩

end Lax342547Proofs.RawBaselines
