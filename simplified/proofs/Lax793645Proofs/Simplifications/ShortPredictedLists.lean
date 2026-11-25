import Lax793645Proofs.Simplifications.PredictedGenerators

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix Submodule LinearMap Function
open scoped BigOperators
noncomputable section
variable {d e : ℕ}

def predictionTriple (α β : F) (X : Cell d) (Y : Cell e) : Signal d e →ₗ[F] PredictedTriple where
  toFun v := (v.1,v.2.1.2+(dotProduct X v.2.1.1.2+α*v.2.1.1.1),
    v.2.2.2+(dotProduct Y v.2.2.1.2+β*v.2.2.1.1))
  map_add' v w := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    all_goals simp only [Prod.fst_add,Prod.snd_add,dotProduct_add,mul_add]; ring
  map_smul' c v := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rfl
    all_goals simp only [Prod.smul_fst,Prod.smul_snd,dotProduct_smul,smul_eq_mul,RingHom.id_apply]; ring

theorem predictionTriple_generator (α β : F) (X : Cell d) (Y : Cell e)
    (r : PredictedTriple) (u : Par d) (v : Par e) :
    predictionTriple α β X Y (predictedGenerator α β X Y r u v)=r := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · change (dotProduct X u.2+α*u.1+r.2.1)+(dotProduct X u.2+α*u.1)=r.2.1
    rw [add_comm _ r.2.1,add_assoc,char_two,add_zero]
  · change (dotProduct Y v.2+β*v.1+r.2.2)+(dotProduct Y v.2+β*v.1)=r.2.2
    rw [add_comm _ r.2.2,add_assoc,char_two,add_zero]

theorem predictionTriple_span (α β : F) (X : Cell d) (Y : Cell e) (R : Set PredictedTriple)
    {v : Signal d e} (hv : v ∈ predictedSpan α β X Y R) :
    predictionTriple α β X Y v ∈ Submodule.span F R := by
  apply (show predictedSpan α β X Y R ≤ (Submodule.span F R).comap
    (predictionTriple α β X Y) from ?_) hv
  apply Submodule.span_le.mpr
  rintro a ⟨r,hr,u,v,rfl⟩
  change predictionTriple α β X Y (predictedGenerator α β X Y r u v) ∈ Submodule.span F R
  rw [predictionTriple_generator]
  exact Submodule.subset_span hr

theorem predicted_coordinates_injective (α β : F) (X : Cell d) (Y : Cell e)
    {u v : Signal d e} (h : predictionTriple α β X Y u=predictionTriple α β X Y v)
    (hA : u.2.1.1=v.2.1.1) (hB : u.2.2.1=v.2.2.1) : u=v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have hh := congrArg (fun a : PredictedTriple => a.1) h
    exact hh
  · refine Prod.ext hA ?_
    have hh := congrArg (fun a : PredictedTriple => a.2.1) h
    change u.2.1.2+(dotProduct X u.2.1.1.2+α*u.2.1.1.1) =
      v.2.1.2+(dotProduct X v.2.1.1.2+α*v.2.1.1.1) at hh
    rw [hA] at hh
    exact add_right_cancel hh
  · refine Prod.ext hB ?_
    have hh := congrArg (fun a : PredictedTriple => a.2.2) h
    change u.2.2.2+(dotProduct Y u.2.2.1.2+β*u.2.2.1.1) =
      v.2.2.2+(dotProduct Y v.2.2.1.2+β*v.2.2.1.1) at hh
    rw [hB] at hh
    exact add_right_cancel hh

theorem triple_span_list (R : Set PredictedTriple) (v : PredictedTriple)
    (hv : v ∈ Submodule.span F R) (hne : v ≠ 0) :
    ∃ (k : ℕ) (r : Fin k → PredictedTriple), 1 ≤ k ∧ k ≤ 3 ∧
      (∀ i, r i ∈ R) ∧ ∑ i, r i = v := by
  classical
  obtain ⟨T,hTR,hspan,hli⟩ := exists_linearIndependent F R
  letI : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T ≤ 3 := by
    simpa [PredictedTriple,Module.finrank_prod] using hli.fintype_card_le_finrank
  have ht : v ∈ Submodule.span F (Set.range (Subtype.val : T → PredictedTriple)) := by
    simpa [Subtype.range_coe,hspan] using hv
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp ht
  let S := Finset.univ.filter (fun t : T => c t=1)
  have hsum : ∑ t ∈ S, t.val = v := by
    rw [←hc]
    unfold S
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    rcases bit_cases (c t) with h | h <;> simp [h]
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at hsum
    exact hne hsum.symm
  let f := Fintype.equivFin (↑S)
  let k := Fintype.card (↑S)
  let r : Fin k → PredictedTriple := fun i => (f.symm i).val.val
  have hi : (∑ i : Fin k, r i) = ∑ t : ↑S, t.val.val := by
    simpa only [r,Equiv.symm_apply_apply] using (Equiv.sum_comp f r).symm
  refine ⟨k,r,?_,?_,fun i => hTR (f.symm i).val.property,?_⟩
  · simpa only [k,Fintype.card_coe] using Nat.succ_le_iff.mpr (Finset.card_pos.mpr hS)
  · have hb : k ≤ Fintype.card T := by
      simpa only [k,Fintype.card_coe] using Finset.card_le_univ S
    exact hb.trans hcard
  · rw [hi]
    exact (Finset.sum_attach S (fun t : T => t.val)).trans hsum

theorem predicted_three_list (α β : F) (X : Cell d) (Y : Cell e)
    (R : Set PredictedTriple) (v : Signal d e) (hv : v ∈ predictedSpan α β X Y R)
    (hq : v.1=1) :
    ∃ (k : ℕ) (r : Fin k → PredictedTriple) (a : Fin k → Par d) (b : Fin k → Par e),
      1 ≤ k ∧ k ≤ 3 ∧ (∀ i, r i ∈ R) ∧
        (∑ i, predictedGenerator α β X Y (r i) (a i) (b i))=v := by
  classical
  have hne : predictionTriple α β X Y v ≠ 0 := by
    intro h
    have hh := congrArg Prod.fst h
    change v.1=0 at hh
    rw [hq] at hh
    exact one_ne_zero hh
  obtain ⟨k,r,hk,h3,hR,hsum⟩ := triple_span_list R _ (predictionTriple_span α β X Y R hv) hne
  let i0 : Fin k := ⟨0,by omega⟩
  let a : Fin k → Par d := Pi.single i0 v.2.1.1
  let b : Fin k → Par e := Pi.single i0 v.2.2.1
  have hA : ∑ i, a i=v.2.1.1 := by simp [a]
  have hB : ∑ i, b i=v.2.2.1 := by simp [b]
  refine ⟨k,r,a,b,hk,h3,hR,predicted_coordinates_injective α β X Y ?_ ?_ ?_⟩
  · rw [map_sum]
    simp_rw [predictionTriple_generator]
    exact hsum
  · simpa only [Prod.snd_sum,Prod.fst_sum,predictedGenerator] using hA
  · simpa only [Prod.snd_sum,Prod.fst_sum,predictedGenerator] using hB

end
end Lax793645Proofs.Simplifications
