import Lax793645Proofs.Simplifications.RepeatedQueryHits
import Lax793645Proofs.Simplifications.HitScales
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.InformationSmallSetBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
noncomputable section
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I]

/-- One constant controls all cells, down to exponentially small reference mass. -/
theorem uniform_hit_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C : ℝ) (hC : 0≤C) :
    ∃ B α : ℝ, 2≤B ∧ 0<α ∧ α≤1/4 ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt (UnitType p n N)), IsLaw w →
      (∀ i,w i≤bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I → Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i, mapW (x i) (freePart p)=unif) →
      ∀ A : Keys (p:=p) v.t N → Prop, bp (-α*n)≤pr unif A →
      pr w (fun o => B*pr unif A < pr (v.heatMap o x) A) ≤ bp (-10*n) := by
  obtain ⟨s,α,E,hs,hα,hα',hE,hcal⟩ := hit_scales M hM C hC I _ _ (globPort p v.t v.aim)
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
  have hp : 0≤pr (unif : Wgt (Keys (p:=p) v.t N)) A := pr_nonneg unif_law.nz
  have hsmall : bp (num (Fin l)*num I-n) ≤ B*pr unif A/2 := by
    calc _ ≤ bp (-(1/2:ℝ)*n) := bp_le hnom
         _ ≤ bp (-α*n) := bp_le (by nlinarith only [hα',Nat.cast_nonneg (α:=ℝ) n])
         _ ≤ pr unif A := hA
         _ ≤ B*pr unif A/2 := by nlinarith only [hB,hp]
  have h := actual_hit_tail v m hN (α*n) E C B (by positivity) (by linarith) z.frame z.peak
    (by simpa [N, pow_two, mul_assoc] using z.cap) w hw hh x hx hz A
    (by simpa only [neg_mul] using hA) hsmall
  refine h.trans ?_
  have he : 2*bp (E*l)/B^l = bp (1+E*l-(E+21*s+1)*l) := by
    unfold B
    rw [bp_sub, bp_add 1 (E*l), bp_one, bp_mul_nat (E+21*s+1) l]
  rw [he]
  apply bp_le
  nlinarith only [hnl, hl, Nat.cast_nonneg (α:=ℝ) s, Nat.cast_nonneg (α:=ℝ) l]

variable {X : Type} [Fintype X] [Nonempty X]

/-- A set below the resolution can be enlarged because the reference is uniform.
If it is nonempty, each individual reference atom is already below the resolution. -/
theorem uniform_setwise_bound (d : Wgt X) (hd : IsLaw d) (B δ η : ℝ)
    (hB : 0≤B) (hδ : 0<δ) (hδ' : 2*δ<1) (hη : 0≤η)
    (hh : ∀ A : X→Prop, δ≤pr unif A → pr d A≤B*pr unif A+η) :
    ∀ A : X→Prop, pr d A≤B*pr unif A+(2*B*δ+η) := by
  classical
  intro A
  have hu : IsLaw (unif : Wgt X) := unif_law
  have hA0 : 0≤pr (unif : Wgt X) A := pr_nonneg hu.nz
  by_cases hA : δ≤pr unif A
  · have h := hh A hA
    nlinarith only [h,mul_nonneg hB hδ.le]
  by_cases hne : ∃ x,A x
  · obtain ⟨x,hx⟩ := hne
    have hm (y : X) : unif y≤δ := by
      rw [show unif y=unif x from by simp [unif_apply], ←pr_point' unif x]
      exact (pr_mono hu.nz (fun j (h : j=x) => h.symm ▸ hx)).trans (le_of_not_ge hA)
    obtain ⟨Q,hAQ,hQ,hQ'⟩ := expand_event hu A δ hδ' hm (by linarith)
    have he := (pr_mono hd.nz hAQ).trans (hh Q hQ)
    have hmul := mul_le_mul_of_nonneg_left hQ' hB
    nlinarith only [he,hmul,mul_nonneg hB hA0]
  · have he : A=(fun _ => False) := funext fun x => propext (by tauto)
    rw [he,pr_false,pr_false]
    nlinarith only [hη,mul_nonneg hB hδ.le]

theorem query_setwise_from_tails {n N : ℕ} (v : Template p I)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (x : I → Wgt (Knobs p.g n)) (hx : ∀ i, IsLaw (x i))
    (B δ η : ℝ) (hB : 0≤B) (hδ : 0<δ) (hδ' : 2*δ<1) (hη : 0≤η)
    (ht : ∀ A : Keys (p:=p) v.t N → Prop, δ≤pr unif A →
      pr w (fun o => B*pr unif A < pr (v.heatMap o x) A)≤η) :
    ∀ A : Keys (p:=p) v.t N → Prop,
      pr (mixW w (fun o => v.heatMap o x)) A ≤ B*pr unif A+(2*B*δ+η) := by
  have hl (o : UnitType p n N) : IsLaw (v.heatMap o x) := mapW_law (prodW_law hx) _
  apply uniform_setwise_bound _ (mixW_law hw hl) B δ η hB hδ hδ' hη
  intro A hA
  simp only [pr,mixW_avg]
  exact hit_mean_bound w _ hw (fun o => (pr_le_tot (hl o).nz).trans_eq (hl o).total)
    B (pr unif A) η (mul_nonneg hB (pr_nonneg unif_law.nz)) (ht A hA)

theorem query_clipping_from_tails {n N : ℕ} (v : Template p I)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (x : I → Wgt (Knobs p.g n)) (hx : ∀ i, IsLaw (x i))
    (B δ η : ℝ) (hB : 0≤B) (hδ : 0<δ) (hδ' : 2*δ<1) (hη : 0≤η)
    (ht : ∀ A : Keys (p:=p) v.t N → Prop, δ≤pr unif A →
      pr w (fun o => B*pr unif A < pr (v.heatMap o x) A)≤η) :
    ∑ k, max (mixW w (fun o => v.heatMap o x) k-B*unif k) 0 ≤ 2*B*δ+η := by
  classical
  apply clipping_from_setwise
  intro A
  have h := query_setwise_from_tails v w hw x hx B δ η hB hδ hδ' hη ht (·∈A)
  simpa [pr,avg,ind] using h

end
end Lax793645Proofs.Simplifications
