/- The slice comparison is an application of the ordinary query variance
estimate to independent point columns with their tester coordinates fixed. -/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SyntheticSliceComparison

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped BigOperators
noncomputable section

variable {A : Type} [Fintype A]

theorem variance_about_reference (u : Wgt A) (hu : IsLaw u) (f : Wgt A) (c : ℝ) :
    avg u (fun x => (f x-c)^2) =
      avg u (fun x => (f x-avg u f)^2) + (avg u f-c)^2 := by
  rw [avg_var u f hu]
  simp_rw [sub_sq, avg_add, avg_sub, avg_mul, avg_mul', hu.avg_const]
  ring

variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

set_option maxHeartbeats 1200000 in
theorem slice_variance_from_query (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N → Prop) (a : I → Tickets p) (m : Mixer p n)
    (h : 2*num (Full p n)<N) (hj : 1≤p.j) (hn : 2*p.r≤n) (hN : 2*num I-(N:ℝ)≤ -1)
    (k : ℝ) (hk : num (Bool × Comp p.g × I)≤ k) (hK : 2*k-N≤ -1) :
    let V := displayLaw p I N (labGram p l f a)
    let F := fun o => pr (sketchLaw p n a) (fun x => P (drill p (incision p l s f x) o))
    avg (raw m N) (fun o => (F o-pr V P)^2) ≤
      2*netFact (tied (drStage p I) Bool)*twinkle (tied (drStage p I) Bool) k N +
        3*bp (num Bool*num I-n) := by
  classical
  intro V F
  let W := sketchLaw p n a
  let μ := raw m N
  let c := pr V P
  let q : Program p n (drStage p I) (I → Knobs p.g n) :=
    ⟨fun x => drQuery (incision p l s f x), fun x => drQuery (incision p l s f x)⟩
  let T (_ : I → Knobs p.g n) (y : Rack (Comp p.g × I) N) :=
    ind (P (relay (Comp p.g) I N y))
  have hw := sketch_law p n a hn
  have hμ := raw_law m h
  have hV := display_law p (labGram p l f a) N hN
  have hT x y : |T x y|≤1 := by
    unfold T; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hF : F = q.oexpect W T := by
    funext o
    unfold F q Program.oexpect Program.showKey T
    simp_rw [drill_view p]
    rfl
  have hbad := buds p n (fun i => rung p n (a i)) (fun i => ticketFlow n _ hn)
    (J:=Bool)
  change pr (draws Bool W) (fun x => ¬bloom p x) ≤ bp (num Bool*num I-n) at hbad
  have hfree : pr (draws Bool W) (fun x => ¬q.free x) ≤ bp (num Bool*num I-n) := by
    refine le_trans (pr_mono (draws_law hw).nz ?_) hbad
    intro x hx hb
    exact hx ⟨bloom_drill p n x l s f hb, bloom_drill p n x l s f hb⟩
  have hvar := Program.oVar (s:=q) m h T W hw hT k
    (fun i => (port_limit _ i).trans hk) hK _ hfree
  change avg μ (fun o => (q.oexpect W T o-avg μ (q.oexpect W T))^2) ≤ _ at hvar
  rw [←hF] at hvar
  let B (x : I → Knobs p.g n) :=
    avg μ (fun o => ind (P (drill p (incision p l s f x) o)))-c
  have hB x : |B x|≤1 := by
    have h1 : 0≤ avg μ (fun o => ind (P (drill p (incision p l s f x) o))) :=
      avg_nonneg hμ.nz (fun _ => ind_nonneg _)
    have h2 : avg μ (fun o => ind (P (drill p (incision p l s f x) o))) ≤1 :=
      hμ.avg_le (fun _ => ind_le_one _)
    have h3 : 0≤c := pr_nonneg hV.nz
    have h4 : c≤1 := (pr_le_tot hV.nz).trans hV.total.le
    unfold B; rw [abs_le]; constructor <;> linarith
  have hzero (x : Bool → I → Knobs p.g n) (hx : draws Bool W x≠0)
      (hb : bloom p x) (i : Bool) : B (x i)=0 := by
    have he := drill_law p (bloom_incision p n x l s f hb i) m h
    rw [sketch_matrix p l s f m a hj _ (draw_elem x i hx)] at he
    unfold B
    rw [←mapW_avg μ (drill p (incision p l s f (x i))) (fun y => ind (P y)), he]
    exact sub_self _
  have hmean : avg μ F-c=avg W B := by
    unfold F B μ W
    rw [avg_sub, hw.avg_const, avg_avg]
    rfl
  have hbias : (avg μ F-c)^2 ≤ bp (num Bool*num I-n) := by
    rw [hmean, avg_cross_sq]
    refine le_trans ?_ hbad
    unfold avg pr
    apply Finset.sum_le_sum
    intro x _
    change draws Bool W x * (B (x true)*B (x false)) ≤ draws Bool W x * ind (¬bloom p x)
    by_cases hx : draws Bool W x=0
    · simp only [hx, zero_mul, le_refl]
    apply mul_le_mul_of_nonneg_left _ ((draws_law hw).nz _)
    by_cases hb : bloom p x
    · rw [hzero x hx hb true, zero_mul, ind_zero (fun h => h hb)]
    rw [ind_one hb]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (hB _) (hB _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  rw [variance_about_reference μ hμ F (pr V P)]
  change _ ≤ _ at hbias
  linarith only [hvar, hbias]

end
end Lax793645Proofs.Simplifications
