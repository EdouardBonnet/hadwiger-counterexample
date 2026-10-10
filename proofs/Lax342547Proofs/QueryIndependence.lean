import Lax342547.QueryIndependence
import Lax342547Proofs.QueryReference
import Lax342547Proofs.PairedKeys
import Lax342547Proofs.KeySpans
import Lax342547Proofs.TableSpaces

namespace Lax342547Proofs.QueryIndependence
open Lax342547.QueryIndependence

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.QueryReference Lax342547.QuerySlots
open Lax342547.PairedKeys Lax342547.KeySpans Lax342547.TableSpaces Lax342547.ExactPins
open Lax342547.ConcreteGeometry

/--
---
conclusion: Lax342547.QueryIndependence.actual_key_independence
---
-/
theorem actual_key_independence {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i) (a : Component (Tag k) × Bool) :
    Function.Injective ((P.space a).mkQ.comp (keyMap (H := H) W a.1)) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro c hc
    have hp : keyMap W a.1 c ∈ P.space a := (Submodule.Quotient.mk_eq_zero _).mp hc
    have ht : keyMap W a.1 c ∈ tableSpace P a := Lax342547Proofs.TableSpaces.pin_le_table P a hp
    let all : Positions W → Binary := fun p =>
      if h : (W.left p.1 p.2.1 p.2.2).tag ∈ a.1.val then c ⟨p,h⟩ else 0
    have hs : (∑ p : Positions W, all p • ray (H := H) (degree := degree) (labels W) (bases W) p) = keyMap W a.1 c := by
      let active : Positions W → Prop := fun p => (W.left p.1 p.2.1 p.2.2).tag ∈ a.1.val
      have h := Finset.sum_subtype (F := inferInstance) (p := active)
        (Finset.univ.filter active) (by simp)
        (fun p => all p • ray (H := H) (degree := degree) (labels W) (bases W) p)
      rw [Finset.sum_filter] at h
      have hl : (∑ p : Positions W, if active p then all p • ray (H := H) (degree := degree) (labels W) (bases W) p else 0) =
          ∑ p : Positions W, all p • ray (H := H) (degree := degree) (labels W) (bases W) p := by
        apply Finset.sum_congr rfl
        intro p _
        by_cases ha : active p
        · rw [if_pos ha]
        · simp [all, active, ha]
      have hr : (∑ p : {p : Positions W // active p}, all p.val •
          ray (H := H) (degree := degree) (labels W) (bases W) p.val) = keyMap W a.1 c := by
        change (∑ p : ComponentPosition W a.1, all p.val •
          ray (H := H) (degree := degree) (labels W) (bases W) p.val) = _
        unfold keyMap
        apply Finset.sum_congr rfl
        intro p _
        simp only [all, dif_pos p.property]
      exact hl.symm.trans (h.trans hr)
    have hcard (i : Fin 2) : Fintype.card (Σ z, Fin (W.length i z)) ≤ 14 := by
      simp only [Fintype.card_sigma, Fintype.card_fin, Fin.sum_univ_two]
      have h0 := W.short i 0
      have h1 := W.short i 1
      omega
    have hall := Lax342547Proofs.KeySpans.independent_sum P A hA (labels W) (bases W)
      W.left_fresh hcard (fun i x => hfresh i x.1 x.2) a all (by rw [hs]; exact ht)
    have hc0 : c = 0 := by
      funext p
      simpa only [all, dif_pos p.property, Pi.zero_apply] using hall p.val
    simpa only [Submodule.mem_bot] using hc0
  · exact bot_le

end Lax342547Proofs.QueryIndependence
