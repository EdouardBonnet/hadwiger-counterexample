/-
Adapted from OpenAI, openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
Original module: OAI.Combinatorics.HadwigerCounterexample.Main.
Changes: archive package namespace and imports; see references/upstream-construction.json.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ParameterExistence
import Lax793645Proofs.Simplifications.OneConstruction
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FinalContradiction
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerMatching.Main

namespace Lax793645Proofs.Upstream.OAI

/-!
# Counterexamples to Hadwiger's conjecture

The single quadratic frame construction yields arbitrarily large graphs with independence
number at most two and small touching matchings. The matching–minor inequality
then separates their complete-minor order from their ordinary chromatic number.

This formalizes the construction theorem and the ordinary chromatic consequence
in OpenAI, *A counterexample to Hadwiger's conjecture* (September 23, 2026).
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology

variable {p:Shape} {n N M s0 :ℕ} {b: PreparationParameters}
open PreparationParameters

def conflictLowerBound (p: Shape) (m:Mixer p n) (N:ℕ) (b:PreparationParameters) :=
   ∀ w:Wgt (UnitType p n N), b.nascent p N w m → carried w (rawHoles m).unit →
     bp (-200*(N:ℝ))≤ pr (pairW w w) (fun i=>(rawHoles m).conflict i.1 i.2)

set_option maxHeartbeats 1600000 in
theorem eventual_conflict_lower_bound (h:AnalyticParameters p M b s0) :
    ∀ᶠ n : ℕ in atTop,∀ m:Mixer p n,unaryGood m b.pins s0→binaryGood m→conflictLowerBound p m (M*n) b := by
  classical
  let P:= fun n:ℕ=> ∃ (m:Mixer p n),unaryGood m b.pins s0∧binaryGood m∧
    ∃ w:Wgt (UnitType p n (M*n)), b.nascent p (M*n) w m ∧ carried w (rawHoles m).unit ∧
      conflicted p m (M*n) w
  suffices hf : ¬∃ᶠ n:ℕ in atTop,P n by
    have hx := not_frequently.mp hf
    refine hx.mono (fun n hn m hm hv w hw hx=>?_); by_contra! hT
    exact hn ⟨m,hm,hv,w,hw,hx,hT⟩
  intro hc
  have hn := frequently_iff_neBot.mp hc
  obtain ⟨U,hU⟩:= Filter.exists_ultrafilter_le (atTop⊓principal {n|P n})

  let l:Filter ℕ:= U
  have hl : l≤atTop := hU.trans inf_le_left
  have hr : ∀ᶠ n in l,P n :=
    (show ∀ᶠ n in principal {i|P i},P n from Filter.eventually_principal.mpr fun x hx=>hx).filter_mono
      (hU.trans inf_le_right)
  let (n:ℕ) : Nonempty (Mixer p n) := ⟨⟨0,0,0⟩⟩
  obtain ⟨m,hm⟩ := taking hr
  obtain ⟨w,hw⟩ := taking (hm.mono fun i h=> h.2.2)
  have hF : ∀ᶠ n in l, ∃ s : LeafMixture p n (M*n),b.entered p (M*n) (m n) (w n) s := by
    filter_upwards [hw,h.enter.hF.filter_mono hl] with n hn ht
    exact ht _ _ hn.1 hn.2.1
  obtain ⟨s,hS⟩:= taking hF
  obtain ⟨v,hv,hV⟩:= prepare U hl h.enter.first (hw.mono fun i hi=>hi.1) hS
  refine StatusAnalysis.refuteVeil ⟨h,hl,hv,(hm.and hw).mono fun n ⟨h1,h2⟩=>
    ⟨h2.1,h1.1,h1.2.1,h2.2.2⟩⟩ (show NeBot (U:Filter ℕ) from inferInstance) hV

open HadwigerMatching LinearListHadwiger

/-- Arbitrarily large finite graphs of independence number at most two and
touching-matching number less than one hundredth of the number of vertices. -/
theorem exists_graphs (M : ℕ) : ∃ m:ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧
      (connectedMatchingNumber G:ℚ) < (m:ℚ)/100 := by
  exact Lax793645Proofs.Simplifications.OneConstruction.exists_graphs M

/-- Arbitrarily large counterexamples to Hadwiger's conjecture, with the full
rational bounds and finiteness of the ordinary chromatic number. -/
theorem exists_counterexamples (M : ℕ) : ∃ m : ℕ, max M 5 ≤ m ∧
    ∃ G : SimpleGraph (Fin m), G.indepNum ≤ 2 ∧ (connectedMatchingNumber G : ℚ) < (m : ℚ) / 100 ∧
      (hadwigerNumber G : ℚ) < 26 * (m : ℚ) / 75 + 2 / 3 ∧
      26 * (m : ℚ) / 75 + 2 / 3 < (m : ℚ) / 2 ∧ (m : ℚ) / 2 ≤ (G.chromaticNumber.toNat : ℚ) ∧
      hadwigerNumber G < G.chromaticNumber.toNat ∧
      G.chromaticNumber ≠ ⊤ ∧ G.chromaticNumber = ↑(G.chromaticNumber.toNat) := by
  obtain ⟨m,hm,G,ha,hc⟩:= exists_graphs M
  have he : 5≤ m:=(le_max_right ..).trans hm
  have : NeZero m:= ⟨by omega⟩
  have hx:=full_matching_minor_proposition (Fin m) G
  dsimp only at hx
  rw [Fintype.card_fin] at hx
  obtain ⟨h1,h2,h3⟩:= hx.2 ha hc he
  have hk:G.chromaticNumber ≠ ⊤:= by
    intro h; have hs := G.chromaticNumber_le_card; simp [h] at hs
  refine ⟨m,hm,G,ha,hc,h1,h2,h3,?_,hk,?_⟩
  · exact_mod_cast ((h1.trans h2).trans_le h3)
  exact (ENat.natCast_toNat_eq_self.mpr hk).symm

theorem not_hadwiger_conjecture : ¬ (∀ (m:ℕ)(G:SimpleGraph (Fin m)), G.chromaticNumber ≤ ↑(hadwigerNumber G)) := by
  intro h; obtain ⟨m,hM,G,h1,h2,h3,h4,h5,h6,he,hC⟩:=exists_counterexamples 0
  have ht:=h m G; rw [hC] at ht
  exact h6.not_ge (by exact_mod_cast ht)
end HadwigerCounterexample

end

end Lax793645Proofs.Upstream.OAI
