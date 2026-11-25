/-
Adapted from OpenAI's TableInjectionTransfer (Apache-2.0); see the vendored
module for provenance. This finite dictionary argument has no construction
or frame-law assumptions.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.TableInjectionTransfer

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [Fintype A]

set_option maxHeartbeats 600000 in
theorem named_fans_transfer {P : A×A→Prop} (fans : A→A→Prop)
    {C U l R : ℝ} (hP : named P C) (hu : 0<U) (hℓ : 0<l) (hR : 0≤R)
    (w : Wgt A) (hw : IsLaw w)
    (htail : ∀ S : A→Prop,U≤pr w S→
      pr w (fun y=>3*l≤pr (onW w S) (fun x=>fans x y))≤R) :
    pr (pairW w w) (fun x=>P x ∧ fans x.1 x.2)≤
      3*l*pr (pairW w w) P+U+C*R := by
  classical
  obtain ⟨t,hC,S,hS⟩ := hP
  let v := onW w
  let f := fans
  let event (y : A) :=
    ∃ a : Fin t,U≤pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
  have he : pr w event ≤ C * R := by
    let Q (a : Fin t) := fun y => U ≤ pr w (S a) ∧ 3*l≤pr (v (S a)) (fun x => f x y)
    have h a : pr w (Q a) ≤ R := by
      by_cases ht : U≤pr w (S a)
      · simp only [Q,ht,true_and]
        exact htail (S a) ht
      simp only [Q,ht,false_and,pr_false]; exact hR
    refine (pr_exists_le hw.nz Q).trans ?_
    refine (Finset.sum_le_sum fun i _ => h i).trans ?_
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hC hR
  have hU (y : A) :
      pr w (fun x => P (x,y) ∧ f x y) ≤ 3*l*pr w (fun x => P (x,y)) + U + ind (event y) := by
    obtain ⟨a,ha⟩ := hS y
    simp_rw [ha]
    have h1 := pr_nonneg (p:=S a) hw.nz
    have hr := mul_nonneg (show 0≤3*l by linarith) h1
    by_cases h : U≤pr w (S a)
    · by_cases ht : 3*l ≤ pr (v (S a)) (fun x => f x y)
      · rw [ind_one (show event y from ⟨a,h,ht⟩)]
        exact ((pr_le_tot hw.nz).trans hw.total.le).trans (by linarith only [hr,hu])
      rw [pr_of_on hw.nz]
      have hj := mul_le_mul_of_nonneg_left (le_of_not_ge ht) h1
      have hi := ind_nonneg (event y)
      refine hj.trans ?_
      linarith only [hi,hu]
    have hh := (pr_mono hw.nz (p:=fun x => S a x∧ f x y) (q:=S a) fun x h => h.1).trans
      (le_of_not_ge h)
    refine hh.trans ?_
    linarith only [hr,ind_nonneg (event y)]
  rw [pair_each,pair_each]
  apply (avg_mono hw.nz hU).trans
  rw [avg_add,avg_add,avg_mul',hw.avg_const]
  exact add_le_add_right he _

end
end Lax793645Proofs.Simplifications
