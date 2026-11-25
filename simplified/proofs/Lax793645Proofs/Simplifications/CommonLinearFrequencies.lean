import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Module Submodule Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I Λ : Type} [Fintype I] [Fintype Λ]

/-- A basis of the frequent characters has bounded expected occupancy.
Independent leaves seldom share any character outside its span. -/
theorem shared_leaf_frequencies (μ : Wgt Λ) (hμ : IsLaw μ)
    (W : Λ → Space (Vec I)) (r : ℕ) (hr : ∀ l,dim (W l) ≤ r)
    (η : ℝ) (hη : 0 < η) :
    ∃ H : Space (Vec I), (dim H : ℝ) ≤ r * bp r / η ∧
      pr (pairW μ μ) (fun l => ¬ W l.1 ⊓ W l.2 ≤ H) ≤ η := by
  classical
  let ε := η / bp r
  have hε : 0 < ε := div_pos hη (bp_pos _)
  let frequent : Set (Vec I) := {x | ε < pr μ (fun l => x ∈ W l)}
  let H := Submodule.span F frequent
  obtain ⟨S,hS,hcard,_,hli⟩ := Submodule.exists_finset_span_eq_linearIndepOn F frequent
  have hcount (l : Λ) : ∑ x ∈ S, ind (x ∈ W l) ≤ (r:ℝ) := by
    let T := S.filter fun x => x ∈ W l
    have hTS : (T : Set (Vec I)) ⊆ S := fun _ hx => (mem_filter.mp hx).1
    have hspan : Submodule.span F (T : Set (Vec I)) ≤ W l :=
      Submodule.span_le.mpr fun _ hx => (mem_filter.mp hx).2
    have hT : T.card ≤ r := by
      rw [←finrank_span_finset_eq_card (hli.mono hTS)]
      exact (Submodule.finrank_mono hspan).trans (hr l)
    have he : (T.card : ℝ) = ∑ x ∈ S, ind (x ∈ W l) := by
      calc
        _ = ∑ _x ∈ T, (1:ℝ) := by simp
        _ = _ := by rw [show T = S.filter (fun x => x ∈ W l) from rfl, Finset.sum_filter]; rfl
    rw [←he]
    exact_mod_cast hT
  have hsize : (dim H : ℝ) * ε ≤ r := calc
    _ = ∑ _x ∈ S, ε := by simp [hcard,H]
    _ ≤ ∑ x ∈ S, pr μ (fun l => x ∈ W l) :=
      sum_le_sum fun x hx => (show ε < _ from hS hx).le
    _ = avg μ (fun l => ∑ x ∈ S, ind (x ∈ W l)) := (avg_sum ..).symm
    _ ≤ _ := hμ.avg_le hcount
  have rare (x : Vec I) (hx : x ∉ H) : pr μ (fun l => x ∈ W l) ≤ ε :=
    le_of_not_gt fun hf => hx (subset_span (show x ∈ frequent from hf))
  refine ⟨H, ?_, ?_⟩
  · apply (le_div_iff₀ hη).mpr
    calc
      (dim H : ℝ) * η = ((dim H : ℝ) * ε) * bp r := by
        dsimp [ε]
        field_simp [(bp_pos _).ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize (bp_pos _).le
  · rw [pr,pairW_avg]
    apply hμ.avg_le
    intro l
    let : Fintype (W l) := Fintype.ofFinite _
    have hex (l' : Λ) (h : ¬ W l ⊓ W l' ≤ H) :
        ∃ x : W l, (x : Vec I) ∉ H ∧ (x : Vec I) ∈ W l' := by
      obtain ⟨x,hx,hout⟩ := Set.not_subset.mp h
      exact ⟨⟨x,hx.1⟩,hout,hx.2⟩
    have hb (x : W l) : pr μ (fun l' => (x : Vec I) ∉ H ∧ (x : Vec I) ∈ W l') ≤ ε := by
      by_cases hx : (x : Vec I) ∈ H
      · simpa [hx,pr_false] using hε.le
      · exact (pr_mono hμ.nz (fun _ h => h.2)).trans (rare x hx)
    change pr μ (fun l' => ¬ W l ⊓ W l' ≤ H) ≤ η
    calc
      _ ≤ _ := (pr_mono hμ.nz hex).trans (pr_exists_le hμ.nz _)
      _ ≤ ∑ _ : W l, ε := sum_le_sum fun x _ => hb x
      _ = (Fintype.card (W l) : ℝ) * ε := by simp
      _ ≤ bp r * ε := mul_le_mul_of_nonneg_right (by rw [card_space]; exact bp_le (by exact_mod_cast hr l)) hε.le
      _ = η := mul_div_cancel₀ _ (bp_pos _).ne'

/-- Adding a coset that meets W increases the captured dimension by one. -/
theorem intersection_adjoin_gain (W H : Space (Vec I)) (x : Vec I)
    (hx : x∉H) (hWx : x∈W⊔H) :
    dim (W⊓(H⊔Submodule.span F {x}) : Space (Vec I))=dim (W⊓H : Space (Vec I))+1 := by
  have hsup : W⊔(H⊔Submodule.span F {x})=W⊔H := by
    rw [←sup_assoc]
    exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem x (W⊔H)).mpr hWx)
  have ha := Submodule.finrank_sup_add_finrank_inf_eq W H
  have hb := Submodule.finrank_sup_add_finrank_inf_eq W (H⊔Submodule.span F {x})
  have hc := Submodule.finrank_sup_span_singleton hx
  rw [hsup] at hb
  dsimp only [dim]
  omega

def frequencyEnergy (μ : Wgt Λ) (W : Λ→Space (Vec I)) (H : Space (Vec I)) : ℝ :=
  avg μ (fun l=>(dim (W l⊓H : Space (Vec I)):ℝ))

/-- Common linear frequencies can be selected with bounded dimension so
that every remaining nonzero quotient frequency is rare. This is the
quotient formulation: membership is in W_l+H, rather than W_l alone. -/
theorem common_frequency_space (μ : Wgt Λ) (hμ : IsLaw μ)
    (W : Λ→Space (Vec I)) (r : ℕ) (hr : ∀ l,dim (W l)≤r)
    (ε : ℝ) (_hε : 0<ε) :
    ∃ H : Space (Vec I),ε*(dim H:ℝ)≤r ∧
      ∀ x : Vec I,x∉H→pr μ (fun l=>x∈W l⊔H)≤ε := by
  classical
  let : Finite (Space (Vec I)) := Finite.of_injective
    (fun H : Space (Vec I)=>(H : Set (Vec I))) SetLike.coe_injective
  let : Fintype (Space (Vec I)) := Fintype.ofFinite _
  let score (H : Space (Vec I)) := frequencyEnergy μ W H-ε*(dim H:ℝ)
  obtain ⟨H,_,hmax⟩ := Finset.exists_max_image univ score (by exact ⟨⊥,mem_univ _⟩)
  have hmax' (H' : Space (Vec I)) : score H'≤score H := hmax H' (mem_univ _)
  have hupper (H' : Space (Vec I)) : frequencyEnergy μ W H'≤r := by
    apply hμ.avg_le
    intro l
    exact_mod_cast (Submodule.finrank_mono (inf_le_left : W l⊓H'≤W l)).trans (hr l)
  have hzero : frequencyEnergy μ W ⊥=0 := by
    have he (l : Λ) : dim (W l⊓⊥ : Space (Vec I))=0 := by
      rw [inf_bot_eq]
      exact finrank_bot _ _
    simp only [frequencyEnergy,he,Nat.cast_zero,avg_zero]
  have hbase : 0≤score H := by
    have hh := hmax' ⊥
    dsimp only [score] at hh ⊢
    rw [hzero,show dim (⊥ : Space (Vec I))=0 from finrank_bot _ _,Nat.cast_zero,
      mul_zero,sub_zero] at hh
    exact hh
  refine ⟨H,by dsimp only [score] at hbase; linarith [hupper H],?_⟩
  intro x hx
  let H' : Space (Vec I) := H⊔Submodule.span F {x}
  have hdim : dim H'=dim H+1 := Submodule.finrank_sup_span_singleton hx
  have hinc : frequencyEnergy μ W H+pr μ (fun l=>x∈W l⊔H)≤frequencyEnergy μ W H' := by
    rw [frequencyEnergy,pr,←avg_add]
    apply avg_mono hμ.nz
    intro l
    by_cases hw : x∈W l⊔H
    · rw [ind_one hw]
      have he := intersection_adjoin_gain (W l) H x hx hw
      exact_mod_cast he.ge
    · rw [ind_zero hw,add_zero]
      exact_mod_cast (Submodule.finrank_mono (inf_le_inf_left (W l) le_sup_left))
  have hm := hmax' H'
  dsimp only [score] at hm
  rw [hdim,Nat.cast_add,Nat.cast_one] at hm
  linarith

/-- The quotient-frequency bound controls intersections after both leaf
partitions have been refined by the common frequency space. The two
leaves are drawn independently. -/
theorem rare_quotient_intersections (μ : Wgt Λ) (hμ : IsLaw μ)
    (W : Λ→Space (Vec I)) (H : Space (Vec I)) (r : ℕ)
    (hr : ∀ l,dim (W l)≤r) (ε : ℝ) (hε : 0≤ε)
    (hrare : ∀ x : Vec I,x∉H→pr μ (fun l=>x∈W l⊔H)≤ε) :
    pr (pairW μ μ) (fun p=>(W p.1⊔H)⊓(W p.2⊔H)≠H)≤bp r*ε := by
  classical
  let Q (l : Λ) : Submodule F ((Vec I)⧸H) := (W l).map H.mkQ
  let : Fintype ((Vec I)⧸H) := Fintype.ofFinite _
  have hmem (x : Vec I) (l : Λ) : H.mkQ x∈Q l ↔ x∈W l⊔H := by
    change x∈Submodule.comap H.mkQ ((W l).map H.mkQ) ↔ _
    rw [Submodule.comap_map_mkQ,sup_comm]
  have hz (x : Vec I) : H.mkQ x=0 ↔ x∈H := by
    exact Submodule.Quotient.mk_eq_zero H
  have hfixed (l : Λ) :
      pr μ (fun l'=>(W l⊔H)⊓(W l'⊔H)≠H)≤bp r*ε := by
    let : Fintype (Q l) := Fintype.ofFinite _
    have he (l' : Λ) (hne : (W l⊔H)⊓(W l'⊔H)≠H) :
        ∃ q : Q l,(q : (Vec I)⧸H)≠0 ∧ (q : (Vec I)⧸H)∈Q l' := by
      have hnot : ¬(W l⊔H)⊓(W l'⊔H)≤H := by
        intro hh
        exact hne (le_antisymm hh (le_inf le_sup_right le_sup_right))
      obtain ⟨x,hx,hout⟩ := Set.not_subset.mp hnot
      refine ⟨⟨H.mkQ x,(hmem x l).mpr hx.1⟩,?_,(hmem x l').mpr hx.2⟩
      exact fun hh=>hout ((hz x).mp hh)
    have hp (q : Q l) :
        pr μ (fun l'=>(q : (Vec I)⧸H)≠0 ∧ (q : (Vec I)⧸H)∈Q l')≤ε := by
      by_cases hq : (q : (Vec I)⧸H)=0
      · simpa only [hq,ne_eq,not_true_eq_false,false_and,pr_false] using hε
      obtain ⟨x,hx⟩ := H.mkQ_surjective (q : (Vec I)⧸H)
      have hout : x∉H := fun hh=>hq (hx.symm.trans ((hz x).mpr hh))
      have hb := hrare x hout
      apply (pr_mono hμ.nz (fun l' hh=>?_) ).trans hb
      exact (hmem x l').mp (hx.symm ▸ hh.2)
    refine ((pr_mono hμ.nz he).trans (pr_exists_le hμ.nz _)).trans ?_
    calc
      _≤∑ _ : Q l,ε := Finset.sum_le_sum (fun q _=>hp q)
      _=(Fintype.card (Q l):ℝ)*ε := by simp
      _≤bp r*ε := by
        apply mul_le_mul_of_nonneg_right ?_ hε
        rw [card_space]
        apply bp_le
        exact_mod_cast (Submodule.finrank_map_le H.mkQ (W l)).trans (hr l)
  rw [pr,pairW_avg]
  exact hμ.avg_le hfixed

/-- Pro's common-frequency lemma, with a dimension bound independent of
the ambient key dimension and the number of leaves. -/
theorem common_linear_intersections (μ : Wgt Λ) (hμ : IsLaw μ)
    (W : Λ→Space (Vec I)) (r : ℕ) (hr : ∀ l,dim (W l)≤r)
    (η : ℝ) (hη : 0<η) :
    ∃ H : Space (Vec I),(dim H:ℝ)≤r*bp r/η ∧
      pr (pairW μ μ) (fun p=>(W p.1⊔H)⊓(W p.2⊔H)≠H)≤η := by
  have he : 0<η/bp r := div_pos hη (bp_pos _)
  obtain ⟨H,hsize,hrare⟩ := common_frequency_space μ hμ W r hr (η/bp r) he
  refine ⟨H,?_,?_⟩
  · apply (le_div_iff₀ hη).mpr
    calc
      (dim H:ℝ)*η=(η/bp r*(dim H:ℝ))*bp r := by
        field_simp [(bp_pos r).ne']
      _≤r*bp r := mul_le_mul_of_nonneg_right hsize (bp_pos r).le
  · have hh := rare_quotient_intersections μ hμ W H r hr (η/bp r) he.le hrare
    simpa only [mul_div_cancel₀ _ (bp_pos r).ne'] using hh

end
end Lax793645Proofs.Simplifications
