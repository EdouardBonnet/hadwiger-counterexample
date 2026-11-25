import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BinaryMixingBounds

/-! The existing binary analytic consumer works with the sharp block for every
same-endpoint parity. This is the interface change required by the explicit
shifted-diagonal construction; the old Z-specific predicate is not assumed. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Template Matrix
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

abbrev binarySharpGood (m : Mixer p n) : Prop := binaryGood m

theorem choral_live_explicit (v : Template p I) (m : Mixer p n) (hm : binarySharpGood m)
    (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (i : v.Chorus) (c : Vec (v.Abbey i)) (hc : c≠0) :
    let j := v.choral.first i
    let l := v.choral.nextP i
    ∃ B, (v.f j).keeps (v.t j) B ∧ (v.f l).keeps (v.t l) B ∧
      n≤5*blockRank B (v.s j) (v.s l) (v.chorusM m x i c) := by
  exact v.choral_live m hm x hx hv i c hc

/-- The original binary mixing bound, now under the explicit construction's
sharp-block hypothesis. Unary mixing and cross-endpoint litFire are unchanged. -/
theorem resonant_explicit [DecidableEq I] (v : Template p I) (m : Mixer p n)
    (hm : binarySharpGood m) (x : UnitType p n N) (hx : litFire p x) (hv : v.diffsel)
    (w : I → Wgt (Knobs p.g n)) (hw : ∀ i, IsLaw (w i))
    (C : ℝ) (hC : 0 < C) (hc : ∀ i j, w i j ≤ C*unif j)
    (s : Script p I) :
    ∀ u : I → Wgt (Knobs p.g n), (∀ i x, |u i x|≤1) →
    |avg (prodW w) (fun z => ind (v.performs s m x z)*prodW u z) -
      v.kappa * ∏ i:I, avg (w i) (u i)| ≤ C^2*bp (-(n:ℝ)/10) := by
  classical
  refine hear_band v.choral (v.chime m x) (v.lyrics s) w hw _
    (mul_nonneg (sq_nonneg _) (bp_pos _).le) ?_
  intro i c hc' a b ha hb
  obtain ⟨B, hB, hB', hz⟩ := choral_live_explicit v m hm x hx hv i c hc'
  simp_rw [vectorPhase, v.chime_seq]
  exact spark_condition _ (v.chorusM m x i c) _ _ _ _ _ _ B hB hB' a b ha hb
    _ _ (hw _) (hw _) C hC (hc _) (hc _) hz

end
end Lax793645Proofs.Simplifications
