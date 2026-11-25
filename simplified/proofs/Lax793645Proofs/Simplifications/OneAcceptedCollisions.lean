import Lax793645Proofs.Simplifications.OneAcceptedRecords
import Lax793645Proofs.Simplifications.OneQueryHistograms
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CollisionInequality

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

def oneSlots (p : Shape) (I : Type) [Fintype I]:=Fintype.card I*tagDegree p.g
def oneMaxSlots (p : Shape):=28*tagDegree p.g

theorem one_keys_dimension (t : Tagging p I) : dim (OneKeys t N)=oneSlots p I*(2*N) := by
  simp only [OneKeys,dim,Module.finrank_pi_fintype,HyperbolicIdx,
    Module.finrank_self,Finset.sum_const,smul_eq_mul,Finset.card_univ,
    Fintype.card_sum,Fintype.card_fin,card_star,mul_one]
  unfold oneSlots
  ring

set_option maxHeartbeats 1200000 in
theorem one_collision_on_accepted_slots (v : A→Volley p n I) (w : B→Volley p n I)
    {t : Tagging p I} (m : Mixer p n)
    {a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)} {μ δ : Wgt (OneUnit p n N)}
    (rhoA : Wgt A) (rhoB : Wgt B)
    (U : A → OneUnit p n N → Prop) (V : B → OneUnit p n N → Prop)
    (ha : ∀ i x, U i x → imagePinAgree oneCoordinateImages a x ∧ (∀ i,oneFrameLaw m (x i)))
    (hb : ∀ i x, V i x → imagePinAgree oneCoordinateImages b x ∧ (∀ i,oneFrameLaw m (x i)))
    {ζ : ℝ} {K : ℕ}
    (h : ∀ i j x,U i x → ∀ y,V j y → oneVolleyKeys (v i) t x=oneVolleyKeys (w j) t y →
      onePromise (v i) (w j) t m a.sp b.sp x y)
    (hv : ∀ i x,U i x → imagePlanRank (a.sp⊔oneKeyPlan (v i) t)=imagePlanRank a.sp+oneSlots p I)
    (hw : ∀ i x,V i x → imagePlanRank (b.sp⊔oneKeyPlan (w i) t)=imagePlanRank b.sp+oneSlots p I)
    (hκ : imagePlanRank a.sp≤K) (hκ' : imagePlanRank b.sp≤K)
    (hz : ζ ≤ 0.004) (hK : ζ*(oneSlots p I) ≤ 0.004) (hslots : oneSlots p I≤oneMaxSlots p)
    (hμ : SubLaw μ) (hδ : SubLaw δ) (hu : SubLaw rhoA) (hu' : SubLaw rhoB)
    (hA : imagePinClear oneCoordinateImages a ζ μ) (hB : imagePinClear oneCoordinateImages b ζ δ)
    (hN : 100 ≤ 2*N) (hT : (dim (OneCheckGram p n) : ℝ) ≤ 0.01*(2*N))
    (hL : (K+(oneMaxSlots p:ℝ))*num (OneColumn p n) ≤ 0.005*(2*N))
    (J : OneKeys t N → Prop) :
    overlap (unifOn J) (oneHistogram v t μ rhoA U) (oneHistogram w t δ rhoB V) ≤
      bp (((oneSlots p I:ℝ)+0.02)*(2*N))*pr (pairW μ δ) (fun x =>
        (oneRawHoles m).conflict (x.1 true,x.1 false) (x.2 true,x.2 false)) + 2*bp (-0.005*(2*N)) := by
  classical
  let k := oneSlots p I
  let L := bp (0.005*(2*N))
  let C := fun (x : OneUnit p n N × OneUnit p n N) =>
    (oneRawHoles m).conflict (x.1 true,x.1 false) (x.2 true,x.2 false)
  let X := oneHistogram v t μ rhoA U
  let Y := oneHistogram w t δ rhoB V
  let H := hit (2*N)*tau (2*N) k*L
  let D := pr (pairW μ δ) C
  let α (u : OneKeys t N) i := pr μ (fun x => U i x ∧ oneVolleyKeys (v i) t x=u)
  let β (u : OneKeys t N) i := pr δ (fun x => V i x ∧ oneVolleyKeys (w i) t x=u)
  have hX u : 0≤ X u := avg_nonneg hu.nz (fun i => pr_nonneg hμ.nz)
  have hY u : 0≤ Y u := avg_nonneg hu'.nz (fun i => pr_nonneg hδ.nz)
  have hW (f : ImagePlan (Comp p.g) (OneColumn p n)) (hk : imagePlanRank f≤K)
      (v : Volley p n I) (hv : imagePlanRank (f⊔oneKeyPlan v t)=imagePlanRank f+oneSlots p I) :
      bp (dim (ImageLedger (f⊔oneKeyPlan v t)))≤L := by
    apply bp_le
    rw [image_ledger_dimension]
    push_cast
    have ht : (imagePlanRank (f⊔oneKeyPlan v t):ℝ)≤K+(oneMaxSlots p:ℝ) := by
      exact_mod_cast (hv ▸ Nat.add_le_add hk hslots)
    exact (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)).trans hL
  have hf (x : A × B) :
      hit (2*N) * (∑ u : OneKeys t N, α u x.1*β u x.2) ≤ D+ 2*H :=
    by
      by_cases hU : ∃ y,U x.1 y
      · obtain ⟨y,hy⟩ := hU
        by_cases hV : ∃ z,V x.2 z
        · obtain ⟨z,hz'⟩ := hV
          exact one_record_sum (v x.1) (w x.2) t m (U _) (V _)
            (ha x.1) (hb x.2) (h x.1 x.2) (hv x.1 y hy) (hw x.2 z hz')
            hz hK hμ hδ hA hB hN hT L
            (hW a.sp hκ _ (hv x.1 y hy)) (hW _ hκ' _ (hw x.2 z hz'))
        have hz' (u) : β u x.2=0 := by
          simp only [β,pr,avg]
          apply Finset.sum_eq_zero
          intro z _
          rw [ind_zero (fun hh => hV ⟨z,hh.1⟩),mul_zero]
        simp_rw [hz',mul_zero,Finset.sum_const_zero,mul_zero]
        exact add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
          (mul_nonneg (by norm_num) (mul_nonneg
            (mul_nonneg (bp_pos _).le (bp_pos _).le) (bp_pos _).le))
      have hz' (u) : α u x.1=0 := by
        simp only [α,pr,avg]
        apply Finset.sum_eq_zero
        intro y _
        rw [ind_zero (fun hh => hU ⟨y,hh.1⟩),mul_zero]
      simp_rw [hz',zero_mul,Finset.sum_const_zero,mul_zero]
      exact add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
        (mul_nonneg (by norm_num) (mul_nonneg
          (mul_nonneg (bp_pos _).le (bp_pos _).le) (bp_pos _).le))
  have hh : hit (2*N) * (∑ u : OneKeys t N,X u * Y u) ≤ D + 2*H := by
    let F := pairW rhoA rhoB
    have hh' : 0 ≤ D+2*H := by
      apply add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le)
        (bp_pos _).le)
    have hl := (subLaw_pair hu hu').avg_le hh' hf
    rw [avg_mul',avg_sum] at hl
    have ht (u : OneKeys t N) :
        X u*Y u=avg F (fun x : A×B => α u x.1*β u x.2) := (pairW_separate ..).symm
    simp_rw [ht]; exact hl
  apply (overlap_count J X Y hX hY).trans
  rw [card_space,one_keys_dimension]
  push_cast
  let Z := bp (((k:ℝ)+0.02)*(2*N))
  have he : Z*hit (2*N) = bp ((k:ℝ)*(2*N)) := by
    unfold Z hit
    rw [←bp_add]
    congr 1
    push_cast
    ring
  have he' : Z*H = bp (-0.005*(2*N)) := by
    unfold H; rw [← mul_assoc,← mul_assoc,he]
    unfold L tau
    rw [←bp_add,←bp_add]
    congr 1
    push_cast
    ring
  change bp ((k:ℝ)*(2*N))*_≤ Z*D+_
  rw [← he, mul_assoc,← he']
  refine (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq ?_
  ring

end
end Lax793645Proofs.Simplifications
