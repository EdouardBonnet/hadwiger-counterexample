/- Finite repartition by bounded records, followed by closed-pin peeling.
Adapted from the vendored Apache-2.0 PartitionSelection proof. -/
import Lax793645Proofs.Simplifications.ImageLeafTrimming

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I J : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] [Fintype J]
  {N c : ℕ} (X : A→C→Mat (Fin N) I) (hc : 1≤c) (cl : ImageClosure C I c)

include hc in
set_option maxHeartbeats 700000 in
theorem image_repartition (w μ : Wgt (A))
    (hw : IsLaw w) (S : Finset A) (D ζ u : ℝ) (hn : 0<N)
    (hz : 0 < ζ) (hz' : ζ < 1)
    (hMu : ∀ a : ImagePin C I N,cl.close a.sp=a.sp → pr μ (imagePinAgree X a) ≤ fee N ((ζ/c)/4) (imagePlanRank a.sp))
    (hcap : ∀ x, w x ≤ bp (D*N)*μ x)
    (f : A → J) (K1 K2 : ℕ)
    (P : Finset A → ImagePin C I N → Prop)
    (h : ∀ i : J, ∃ b : ImagePin C I N,
       (∀ x∈ S,f x=i → imagePinAgree X b x) ∧ cl.close b.sp=b.sp ∧ imagePlanRank b.sp ≤ K1 ∧
       ∀ (c : ImagePin C I N) (G : Finset A), G.Nonempty → (∀ x∈G,x∈S ∧ f x=i) → b.sp ≤ c.sp → P G c)
    (hK : (D+u) + ζ ≤ ((ζ/c)-(ζ/c)/4)*K2) :
    ∃ V : Tiles A, apart V ∧ (∀ G∈V,
      G⊆S ∧ ∃ b,ImageRipe X cl w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b) ∧
      pr w (fun x => x∈S∧ ¬inTiles V x)≤
        (num J*bp (-u*N)) + bp (-ζ*N) := by
  classical
  let F (i : J) := S.filter (fun x => f x=i)
  have hF (i : J) (x : A) : x∈F i ↔ x∈ S ∧ f x=i := mem_filter
  choose b hb hclosed hL hP using h
  let R (G : Finset A) (b : ImagePin C I N) := ImageRipe X cl w μ G b (D+u+K2+1) ζ (K1+K2) ∧ P G b
  let C := bp (-ζ*N); let t := bp (-u*N)
  have ht (i : J) :
      ∃ V : Tiles A, apart V ∧ (∀ G∈V,G⊆F i∧∃ b,R G b) ∧
        pr w (fun x => x∈F i ∧ ¬inTiles V x)≤t+partMass w (F i)*C := by
    let S' := F i
    let v := partW w S'
    by_cases hi : t≤partMass w (F i)
    · have ht := lt_of_lt_of_le (bp_pos _ : 0<t) hi
      have hv : IsLaw v := on_law hw.nz ht
      have hx (x) : v x≤bp ((D+u)*N)*μ x := by
        apply ((on_mon hw.nz (bp_pos _) hi x).trans
          (mul_le_mul_of_nonneg_left (hcap x) (inv_pos_of_pos (bp_pos _)).le)).trans_eq
        rw [add_mul,bp_add,neg_mul,bp_neg,inv_inv]; ring
      obtain ⟨G,hG,hA,hB⟩ :=
        closed_image_partition X hc cl hz hz' hn hMu hx hv.nz S' (b i) (hclosed i)
          (fun x h => hb i x ((hF ..).mp h).1 ((hF ..).mp h).2) hK
      refine ⟨G,hA,fun S h => ?_,?_⟩
      · obtain ⟨hh,b',hp⟩ := hG S h
        obtain ⟨hz,hzm,_⟩ := exists_of_pr_pos hv.nz hp.pos
        obtain ⟨h1,h2⟩ := issued_law w hw.nz ht hh hp.pos
        refine ⟨hh,b',⟨h1,hp.fixpin,hp.closed,(hp.bound.trans (Nat.add_le_add_right (hL _) _)),?_,?_⟩,
          hP i _ _ ⟨hz,hzm⟩ (fun x hx => (hF ..).mp (hh hx)) hp.extendsSp⟩
        · rw [h2]; exact hp.clear
        rw [h2]; exact hp.density
      · rw [pr_of_on hw.nz (fun x => x∈ F i)]
        have hh : pr v (fun x => ¬inTiles G x) = pr v (fun x => x∈F i ∧ ¬inTiles G x) := by
          apply avg_congr
          intro x h; simp only [show x∈F i from (onW_ne h).1,true_and]
        refine le_trans (mul_le_mul_of_nonneg_left (hh.trans_le hB) ht.le) ?_
        exact le_add_of_nonneg_left (bp_pos _).le
    · refine ⟨∅,(fun x S h => ?_),by simp,?_⟩
      · simp at h
      apply le_trans (pr_mono hw.nz (q:=fun x => x∈F i) fun _ => And.left)
        ((le_of_not_ge hi).trans ?_)
      exact le_add_of_nonneg_right (mul_nonneg (pr_nonneg hw.nz) (bp_pos _).le)
  choose V hV h1 h2 using ht
  let G := Finset.univ.biUnion V
  refine ⟨G,?_,?_,?_⟩
  · intro x S hS T hT h hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hT
    obtain rfl : i=j := ((hF ..).mp ((h1 i S hi).1 h)).2.symm.trans
      ((hF ..).mp ((h1 j T hj).1 hx)).2
    exact hV i x S hi T hj h hx
  · intro S h
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨h,h'⟩ := h1 i S hi
    exact ⟨h.trans (Finset.filter_subset _ _),h'⟩
  · let Q (i : J) := fun x : A => x∈ F i ∧ ¬inTiles (V i) x
    have hf x (h : x∈ S∧¬inTiles G x) : ∃ i,Q i x := by
      refine ⟨f x,(hF ..).mpr ⟨h.1,rfl⟩,?_⟩
      rintro ⟨T,hT,h'⟩
      exact h.2 ⟨T,Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ (f x),hT⟩,h'⟩
    refine ((pr_mono hw.nz hf).trans ((pr_exists_le hw.nz Q).trans
      (Finset.sum_le_sum fun i _ => h2 i))).trans ?_
    rw [Finset.sum_add_distrib]
    have ht : (∑ i, partMass w (F i)) ≤ 1 := by
      simp_rw [partMass, hF,sum_pr_tag]
      exact (pr_le_tot hw.nz).trans hw.total.le
    calc (∑ _ : J,t)+∑ i,partMass w (F i)*C ≤ num J*t+1*C := by
           rw [← Finset.sum_mul]
           simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]
           exact add_le_add_right (mul_le_mul_of_nonneg_right ht (bp_pos _).le) _
         _ = _ := by rw [one_mul]

end
end Lax793645Proofs.Simplifications
