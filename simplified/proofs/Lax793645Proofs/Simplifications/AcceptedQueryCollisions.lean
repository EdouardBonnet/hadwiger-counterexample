/-
Adapted from CollisionInequality (OpenAI,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0).
Key independence is needed only for inputs which accept an orientation.
Rejected inputs contribute zero, without renormalizing either input law.
-/
import Lax793645Proofs.Simplifications.QueryRecordBounds
import Lax793645Proofs.Simplifications.AffineKeySlots
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CollisionInequality

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Volley
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]

set_option maxHeartbeats 800000 in
private theorem record_sum_of_slots (v w : Volley p n I) {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ}
    (h : ∀ x,U x → ∀ y,V y → v.keys t x=w.keys t y → v.promised w t m a.sp b.sp x y)
    (hv : planNew a.sp (v.keyPlan t)=kslots p I)
    (hw : planNew b.sp (w.keyPlan t)=kslots p I)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N *
      (∑ u : Keys (p:=p) t N, pr μ (fun x => U x ∧ v.keys t x=u) *
        pr δ (fun x => V x ∧ w.keys t x=u)) ≤
      pr (pairW μ δ) (fun x => (rawHoles m).conflict x.1 x.2)+
      2*(hit N*tau N (kslots p I)*L) := by
  classical
  let X := UnitType p n N
  let T := Keys (p:=p) t N
  let K (u : T) (x : X) := U x ∧ v.keys t x=u
  let K' (u : T) (x : X) := V x ∧ w.keys t x=u
  let H := hit N*tau N (kslots p I)*L
  let P := pairW μ δ
  let C (x : X × X) := (rawHoles m).conflict x.1 x.2
  let G (u : T) (x : X × X) := K u x.1 ∧ K' u x.2 ∧ C x
  rw [Finset.mul_sum]
  have hh (i : Keys (p:=p) t N) :
      hit N * (pr μ (K i) * pr δ (K' i))≤ pr P (G i)+H*(pr μ (K i)+pr δ (K' i)) := by
    apply record_hit_of_slots v w m (K i) (K' i) i _ _ _ hv hw hz hK hμ hδ hA hB hN hT L hLf hLg
    · exact fun x h => ⟨(ha x h.1).1,(ha x h.1).2,h.2⟩
    · exact fun x h => ⟨(hb x h.1).1,(hb x h.1).2,h.2⟩
    exact fun x hx y hy => h x hx.1 y hy.1 (hx.2.trans hy.2.symm)
  refine (Finset.sum_le_sum fun i _ => hh i).trans ?_
  rw [Finset.sum_add_distrib]
  have hi : (∑ i : Keys (p:=p) t N, pr P (G i)) ≤ pr P C := by
    rw [← sum_pr_tag P C (v.keys t ∘ Prod.fst)]
    exact Finset.sum_le_sum fun i _ => pr_mono (subLaw_pair hμ hδ).nz (fun x h => ⟨h.2.2,h.1.2⟩)
  refine add_le_add hi ?_
  have hU : (∑ i : Keys (p:=p) t N, pr μ (K i))≤1 :=
    (sum_pr_tag μ U (v.keys t)).trans_le ((pr_le_tot hμ.nz).trans hμ.total)
  have hV : (∑ i : Keys (p:=p) t N, pr δ (K' i))≤1 :=
    (sum_pr_tag δ V (w.keys t)).trans_le ((pr_le_tot hδ.nz).trans hδ.total)
  have hz : 0 ≤ H := mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le) ((bp_pos _).le.trans hLf)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,mul_comm 2]
  exact mul_le_mul_of_nonneg_left (by linarith only [hU,hV]) hz

set_option maxHeartbeats 1200000 in
theorem collision_on_accepted_slots (v : A→Volley p n I) (w : B→Volley p n I)
    {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (rhoA : Wgt A) (rhoB : Wgt B)
    (U : A → UnitType p n N → Prop) (V : B → UnitType p n N → Prop)
    (ha : ∀ i x, U i x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ i x, V i x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {K : ℕ}
    (h : ∀ i j x,U i x → ∀ y,V j y → (v i).keys t x=(w j).keys t y →
      (v i).promised (w j) t m a.sp b.sp x y)
    (hv : ∀ i x,U i x → planNew a.sp ((v i).keyPlan t)=kslots p I)
    (hw : ∀ i x,V i x → planNew b.sp ((w i).keyPlan t)=kslots p I)
    (hκ : planRank a.sp≤K) (hκ' : planRank b.sp≤K)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004) (hslots : kslots p I≤kmax p)
    (hμ : SubLaw μ) (hδ : SubLaw δ) (hu : SubLaw rhoA) (hu' : SubLaw rhoB)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (hL : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N)
    (J : Keys (p:=p) t N → Prop) :
    overlap (unifOn J) (hist v t μ rhoA U) (hist w t δ rhoB V) ≤
      bp (((kslots p I:ℝ)+0.02)*N)*pr (pairW μ δ) (fun x =>
        (rawHoles m).conflict x.1 x.2) + 2*bp (-0.005*N) := by
  classical
  let k := kslots p I
  let L := bp (0.005*N)
  let C := fun (x : UnitType p n N × _) => (rawHoles m).conflict x.1 x.2
  let X := hist v t μ rhoA U
  let Y := hist w t δ rhoB V
  let H := hit N*tau N k*L
  let D := pr (pairW μ δ) C
  let α (u : Keys (p:=p) t N) i := pr μ (fun x => U i x ∧ (v i).keys t x=u)
  let β (u : Keys (p:=p) t N) i := pr δ (fun x => V i x ∧ (w i).keys t x=u)
  have hX u : 0≤ X u := avg_nonneg hu.nz (fun i => pr_nonneg hμ.nz)
  have hY u : 0≤ Y u := avg_nonneg hu'.nz (fun i => pr_nonneg hδ.nz)
  have hW (f : Plan p n) (hk : planRank f ≤ K) (v : Volley p n I) (hv : planNew f (v.keyPlan t)=kslots p I) :
      bp (dim (Ledger (v.frozen f t)))≤L := by
    apply bp_le
    rw [ledger_dim]
    push_cast
    have ht : (planRank (v.frozen f t) : ℝ) ≤ K+(kmax p:ℝ) := by
      have hh := plan_add_rank f (v.keyPlan t)
      rw [hv] at hh
      exact_mod_cast (show planRank (f⊔v.keyPlan t) ≤ K+kmax p from
        hh.symm ▸ add_le_add hk hslots)
    exact le_trans (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)) hL
  have hf (x : A × B) :
      hit N * (∑ u : Keys (p:=p) t N, α u x.1*β u x.2) ≤ D+ 2*H :=
    by
      by_cases hU : ∃ y,U x.1 y
      · obtain ⟨y,hy⟩ := hU
        by_cases hV : ∃ z,V x.2 z
        · obtain ⟨z,hz'⟩ := hV
          exact record_sum_of_slots (v x.1) (w x.2) m (U _) (V _)
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
  have hh : hit N * (∑ u : Keys (p:=p) t N,X u * Y u) ≤ D + 2*H := by
    let F := pairW rhoA rhoB
    have hh' : 0 ≤ D+2*H := by
      apply add_nonneg (pr_nonneg (subLaw_pair hμ hδ).nz)
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (bp_pos _).le (bp_pos _).le)
        (bp_pos _).le)
    have hl := (subLaw_pair hu hu').avg_le hh' hf
    rw [avg_mul',avg_sum] at hl
    have ht (u : Keys (p:=p) t N) :
        X u*Y u=avg F (fun x : A×B => α u x.1*β u x.2) := (pairW_separate ..).symm
    simp_rw [ht]; exact hl
  apply (overlap_count J X Y hX hY).trans
  rw [card_space,dim_keys,Nat.cast_mul]
  let Z := bp (((k:ℝ)+0.02)*N)
  have he : Z*hit N = bp ((k:ℝ)*N) := by
    unfold Z hit; rw [← bp_add]; congr 1; ring
  have he' : Z*H = bp (-0.005*N) := by
    unfold H; rw [← mul_assoc,← mul_assoc,he]
    unfold L tau
    rw [← bp_add,← bp_add]; congr 1; ring
  change bp ((k:ℝ)*N)*_≤ Z*D+_
  rw [← he, mul_assoc,← he']
  refine (mul_le_mul_of_nonneg_left hh (bp_pos _).le).trans_eq ?_
  ring
/-- The affine protection condition may be imposed as an input rejection
flag. It is required only on accepted inputs. -/
theorem affine_collision (v : A→Volley p n I) (w : B→Volley p n I)
    {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (rhoA : Wgt A) (rhoB : Wgt B)
    (U : A → UnitType p n N → Prop) (V : B → UnitType p n N → Prop)
    (ha : ∀ i x, U i x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    (hb : ∀ i x, V i x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)))
    {ζ : ℝ} {q K : ℕ}
    (h : ∀ i j x,U i x → ∀ y,V j y → (v i).keys t x=(w j).keys t y →
      (v i).promised (w j) t m a.sp b.sp x y)
    (hv : ∀ i x,U i x → affineAvoids (v i) a.sp q)
    (hw : ∀ i x,V i x → affineAvoids (w i) b.sp q)
    (hκ : planRank a.sp≤K) (hκ' : planRank b.sp≤K)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004) (hslots : kslots p I≤kmax p)
    (hμ : SubLaw μ) (hδ : SubLaw δ) (hu : SubLaw rhoA) (hu' : SubLaw rhoB)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (hL : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N)
    (J : Keys (p:=p) t N → Prop) :
    overlap (unifOn J) (hist v t μ rhoA U) (hist w t δ rhoB V) ≤
      bp (((kslots p I:ℝ)+0.02)*N)*pr (pairW μ δ) (fun x =>
        (rawHoles m).conflict x.1 x.2) + 2*bp (-0.005*N) := by
  exact collision_on_accepted_slots v w m rhoA rhoB U V ha hb h
    (fun i x hx => affine_key_slots (v i) t (hv i x hx))
    (fun i x hx => affine_key_slots (w i) t (hw i x hx))
    hκ hκ' hz hK hslots hμ hδ hu hu' hA hB hN hT hL J

end
end Lax793645Proofs.Simplifications
