import Lax793645Proofs.Simplifications.OneRepeatedQueryHits
import Lax793645Proofs.Simplifications.OneHitScales
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.InformationSmallSetBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I]

/-- One constant controls all cells, down to exponentially small reference mass. -/
theorem one_uniform_hit_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C : ℝ) (hC : 0≤C) :
    ∃ B α : ℝ, 2≤B ∧ 0<α ∧ α≤1/4 ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (m : Mixer p n), Fintype.card (Row p n)+2*p.h+3≤N →
      ∀ (w : Wgt (OneUnit p n N)), IsLaw w →
      (∀ i,w i≤bp (C*N)*oneUnitRaw m N i) →
      ∀ (x : I → Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i, mapW (x i) (freePart p)=unif) →
      ∀ A : OneKeys v.t N → Prop, bp (-α*n)≤pr unif A →
      pr w (fun o => B*pr unif A < pr (oneHeatMap v o x) A) ≤ bp (-10*n) := by
  obtain ⟨s,α,E,hs,hα,hα',hE,hcal⟩ := one_hit_scales M hM C hC I _ _ (globPort p v.t v.aim)
  let B := bp (E+21*s+1)
  have hB : 2≤B := by
    rw [←bp_one]
    apply bp_le
    nlinarith only [hE, Nat.cast_nonneg (α:=ℝ) s]
  refine ⟨B,α,hB,hα,hα',?_⟩
  filter_upwards [hcal] with n hn N m hN w hw hh x hx hz A hA
  obtain ⟨hnl,hnom,z⟩ := hn
  let l := n/s
  have hl : 1≤(l:ℝ) := by exact_mod_cast z.pos
  have hp : 0≤pr (unif : Wgt (OneKeys v.t N)) A := pr_nonneg unif_law.nz
  have hsmall : bp (num (Fin l)*num I-n) ≤ B*pr unif A/2 := by
    calc _ ≤ bp (-(1/2:ℝ)*n) := bp_le hnom
         _ ≤ bp (-α*n) := bp_le (by nlinarith only [hα',Nat.cast_nonneg (α:=ℝ) n])
         _ ≤ pr unif A := hA
         _ ≤ B*pr unif A/2 := by nlinarith only [hB,hp]
  have h := one_actual_hit_tail v m hN (α*n) E C B (by positivity) (by linarith) z.frame z.peak
    (by simpa [N, pow_two, mul_assoc] using z.cap) w hw hh x hx hz A
    (by simpa only [neg_mul] using hA) hsmall
  refine h.trans ?_
  have he : 2*bp (E*l)/B^l = bp (1+E*l-(E+21*s+1)*l) := by
    unfold B
    rw [bp_sub, bp_add 1 (E*l), bp_one, bp_mul_nat (E+21*s+1) l]
  rw [he]
  apply bp_le
  nlinarith only [hnl, hl, Nat.cast_nonneg (α:=ℝ) s, Nat.cast_nonneg (α:=ℝ) l]


end
end Lax793645Proofs.Simplifications
