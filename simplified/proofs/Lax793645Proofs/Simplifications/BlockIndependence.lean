/-
Conditional block independence for repeated query hits. Replacing just one
nonzero coefficient block by its uniform law pays the density cap once.
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GroupedQueryIndependence
import Mathlib.Tactic
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function
open scoped BigOperators
noncomputable section
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

def flattenBlocks : (J → Mat U I) →ₗ[F] Mat U (J × I) where
  toFun B u v := B v.1 u v.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem block_single_eval
    (j : J) (i : I) (u : Vec U) (c : Vec (J × I)) :
    flattenBlocks (Pi.single j (vecMulVec u (Pi.single i 1))) *ᵥ c = c (j,i) • u := by
  funext v
  change (∑ z : J × I, (Pi.single j (vecMulVec u (Pi.single i 1)) : J → Mat U I) z.1 v z.2*c z) = c (j,i)*u v
  rw [Fintype.sum_prod_type,Finset.sum_eq_single j]
  · simp [Pi.single_apply,vecMulVec_apply,mul_comm]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

theorem one_block_cap (w : J → Wgt (Mat U I)) (hw : ∀ j, IsLaw (w j))
    {C : ℝ} (hC : 0 ≤ C) (j : J) (hc : ∀ M, w j M ≤ C*unif M) :
    ∃ v : Wgt (J → Mat U I), IsLaw v ∧
      (∀ B, prodW w B ≤ C*v B) ∧
      (∀ B (T : Mat U I), v (B+Pi.single j T)=v B) := by
  classical
  let w' (k : J) : Wgt (Mat U I) := if k=j then unif else w k
  refine ⟨prodW w',prodW_law (fun k => by dsimp [w']; split_ifs; exact unif_law; exact hw k),?_,?_⟩
  · intro B
    have he : (∏ k ∈ Finset.univ.erase j, w k (B k)) =
        ∏ k ∈ Finset.univ.erase j, w' k (B k) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp [w',(Finset.mem_erase.mp hk).1]
    change (∏ k, w k (B k)) ≤ C*(∏ k, w' k (B k))
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j),
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ j),← he]
    have hn : 0 ≤ ∏ k ∈ Finset.univ.erase j, w k (B k) :=
      Finset.prod_nonneg (fun k _ => (hw k).nz _)
    have hh := mul_le_mul_of_nonneg_left (hc (B j)) hn
    simpa [w',mul_left_comm,mul_assoc] using hh
  · intro B T
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : k=j
    · subst k; simp [w',unif_apply]
    · simp [w',hk,Pi.single_eq_of_ne hk]

theorem block_parity_cap (w : J → Wgt (Mat U I)) (hw : ∀ j, IsLaw (w j))
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ j M, w j M ≤ C*unif M)
    {c : Vec (J × I)} (hc0 : c ≠ 0) (y : Vec U) :
    pr (prodW w) (fun B => flattenBlocks B *ᵥ c=y) ≤ C*bp (-num U) := by
  classical
  obtain ⟨⟨j,i⟩,hi⟩ : ∃ v, c v ≠ 0 := Function.ne_iff.mp hc0
  have hi1 : c (j,i)=1 := (bit_cases _).resolve_left hi
  obtain ⟨v,hv,hdom,hshift⟩ := one_block_cap w hw hC j (hc j)
  let f : (J → Mat U I) →ₗ[F] Vec U :=
    ((Matrix.mulVecBilin F F).flip c).comp flattenBlocks
  have hp := translate_cap hv.sub f (Function.Embedding.refl (Vec U)) (fun u =>
    ⟨Pi.single j (vecMulVec u (Pi.single i 1)),by
      change flattenBlocks _ *ᵥ c=u
      rw [block_single_eval,hi1,one_smul],fun B => hshift B _⟩) y
  have hsize : (Fintype.card (Vec U):ℝ)⁻¹=bp (-num U) := by
    rw [card_space,dim_vec,bp_neg]
  have hp' : pr v (fun B => flattenBlocks B *ᵥ c=y) ≤ bp (-num U) := by
    change pr v (fun B => flattenBlocks B *ᵥ c=y) ≤ (Fintype.card (Vec U):ℝ)⁻¹ at hp
    rwa [hsize] at hp
  exact (pr_cap hdom _).trans (mul_le_mul_of_nonneg_left hp' hC)

theorem independent_block_failure (w : J → Wgt (Mat U I)) (hw : ∀ j, IsLaw (w j))
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ j M, w j M ≤ C*unif M) :
    pr (prodW w) (fun B => ¬Injective (flattenBlocks B).mulVec) ≤
      C*bp (num J*num I-num U) := by
  classical
  let P (c : Vec (J × I)) (B : J → Mat U I) := c≠0 ∧ flattenBlocks B *ᵥ c=0
  have hsub : pr (prodW w) (fun B => ¬Injective (flattenBlocks B).mulVec) ≤
      ∑ c : Vec (J × I), pr (prodW w) (P c) := by
    refine (pr_mono (prodW_law hw).nz (fun B hb => ?_)).trans (pr_exists_le (prodW_law hw).nz P)
    rw [← coe_mulVecLin,← ker_eq_bot,ker_mulVecLin_eq_bot_iff] at hb
    push Not at hb
    obtain ⟨c,hc',hc0⟩ := hb
    exact ⟨c,hc0,hc'⟩
  have hp (c : Vec (J × I)) : pr (prodW w) (P c) ≤ C*bp (-num U) := by
    by_cases h : c=0
    · simp only [P,h,ne_eq,not_true,false_and,pr_false]
      exact mul_nonneg hC (bp_pos _).le
    · simpa only [P,ne_eq,h,not_false_eq_true,true_and] using block_parity_cap w hw hC hc h 0
  refine hsub.trans ((Finset.sum_le_sum (fun c _ => hp c)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,dim_vec,
    Fintype.card_prod,Nat.cast_mul]
  rw [mul_left_comm,← bp_add]
  congr 1

theorem repeated_condition {X : Type} [Fintype X] (w : Wgt X) (P : X → Prop) :
    onW (draws J w) (fun x => ∀ j, P (x j)) = draws J (onW w P) := by
  classical
  have hp : pr (draws J w) (fun x => ∀ j, P (x j))=(pr w P)^Fintype.card J := by
    simpa only [draws,Finset.prod_const,Finset.card_univ] using prodW_pr (fun _ : J => w) (fun _ => P)
  funext x
  rw [onW_val,hp]
  simp only [onW_val,draws,prodW,ind_all,Finset.prod_div_distrib,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

theorem repeated_hit_factor {X : Type} [Fintype X] (w : Wgt X) (hw : IsLaw w)
    (P : X → Prop) (Q : (J → X) → Prop) :
    pr (draws J w) (fun x => (∀ j, P (x j)) ∧ Q x) =
      (pr w P)^Fintype.card J*pr (draws J (onW w P)) Q := by
  rw [pr_of_on (draws_law hw).nz,repeated_condition]
  have hp : pr (draws J w) (fun x => ∀ j, P (x j))=(pr w P)^Fintype.card J := by
    simpa only [draws,Finset.prod_const,Finset.card_univ] using prodW_pr (fun _ : J => w) (fun _ => P)
  rw [hp]

/-- Conditioning each independent query on a hit costs its density factor
only once in the rank union bound, rather than once per query. -/
theorem hit_conditioned_failure {X : Type} [Fintype X] (w : Wgt X) (hw : IsLaw w)
    (Z : X → Mat U I) (hZ : mapW w Z=unif) (P : X → Prop) (hp : 0 < pr w P) :
    pr (draws J (onW w P)) (fun x => ¬Injective (flattenBlocks (Z ∘ x)).mulVec) ≤
      (pr w P)⁻¹*bp (num J*num I-num U) := by
  classical
  have hW : IsLaw (onW w P) := normW_law (subW_nonneg hw.nz P) hp
  have hc B : mapW (onW w P) Z B ≤ (pr w P)⁻¹*unif B := by
    have h := mapW_cap (on_mon hw.nz hp le_rfl) Z B
    rwa [hZ] at h
  have he : mapW (draws J (onW w P)) (fun x => Z ∘ x)=
      prodW (fun _ : J => mapW (onW w P) Z) := mapW_repeat (fun _ : J => onW w P) (fun _ => Z)
  rw [← mapW_pr _ (fun x => Z ∘ x) (fun B => ¬Injective (flattenBlocks B).mulVec),he]
  exact independent_block_failure _ (fun _ => mapW_law hW Z) (inv_nonneg.mpr hp.le) (fun _ => hc)

theorem hit_and_independence_lower {X : Type} [Fintype X]
    (w : Wgt X) (hw : IsLaw w) (Z : X → Mat U I) (hZ : mapW w Z=unif)
    (P : X → Prop) (hp : 0 < pr w P)
    (hsmall : bp (num J*num I-num U) ≤ pr w P/2) :
    (pr w P)^Fintype.card J/2 ≤ pr (draws J w)
      (fun x => (∀ j, P (x j)) ∧ Injective (flattenBlocks (Z ∘ x)).mulVec) := by
  have hW : IsLaw (onW w P) := normW_law (subW_nonneg hw.nz P) hp
  have hf := hit_conditioned_failure (J:=J) w hw Z hZ P hp
  have hD : IsLaw (draws J (onW w P)) := draws_law hW
  rw [pr_not,hD.total] at hf
  have hh : (pr w P)⁻¹*bp (num J*num I-num U) ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hp.le)
    have he : (pr w P)⁻¹*(pr w P/2)=(1:ℝ)/2 := by field_simp
    rwa [he] at h
  rw [repeated_hit_factor w hw]
  have h := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ pr (draws J (onW w P))
    (fun x => Injective (flattenBlocks (Z ∘ x)).mulVec) by linarith)
    (pow_nonneg hp.le (Fintype.card J))
  linarith
end
end Lax793645Proofs.Simplifications
