/-
Adapted finite scale/refinement calculations from OpenAI, openai/math,
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
The new proofs use repeated hits and quadratic energy instead of entropy.
-/
import Lax793645Proofs.Simplifications.QuadraticProjection

/-! Finite nets from quadratic increments, with rounded small cells. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
noncomputable section
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable {μ : Wgt A} {p : A→Wgt B}

set_option maxHeartbeats 1000000 in
theorem quadratic_divide_progress [Nonempty B] (h : Ultra μ p)
    (ε δ α k : ℝ) (hε : 0<ε) (hk : 0<k) (hk' : 2*k≤1)
    (hδ : 0<δ) (hα : δ≤1)
    (hB : ∀ P : B→ Prop, pr unif P ≤α → pr (mixW μ p) P ≤ε)
    (f : B→ C) (hz : stamina (mapW unif f) δ)
    (hC : num (C×Bool)*k ≤min α ε)
    (w : Wgt B) (hw : catalog μ p w) (hr : 8*ε<varOne w (bucket unif f w)) :
    ∃ F : B → C×Bool, stamina (mapW unif F) (k*δ) ∧
      quadraticBudget μ p f + ε^2 ≤ quadraticBudget μ p F := by
  classical
  let q : Wgt B := unif
  have hq : IsLaw q := unif_law
  let v := bucket q f w
  have ht := h.cat_sub w hw
  let P (i : B) := v i < w i
  have hv (i) : 0≤v i := pour_nz _ hq.nz (map_nz ht.nz f) i
  have hh : varOne w v=2*(pr w P-pr v P) := by
    have hx : lsupp w q := fun i _ => by unfold q; rw [unif_apply]; positivity
    exact var_event w v (by rw [←map_mass w f,←map_mass v f,bucket_scale q w hq.nz hx])
  obtain ⟨F,hF,hφ,hL⟩ := divide_fit q hq f P δ (k*δ) (by positivity)
    ((le_of_eq (by rw [← mul_assoc])).trans ((mul_le_mul_of_nonneg_right hk' hδ.le).trans_eq
      (one_mul _))) hz
  refine ⟨F,hφ,?_⟩
  let Q := fun i : B => ((F i).2=true)
  let S := fun i => ¬(P i ↔ Q i)
  have h1 : pr w S ≤ ε := by
    obtain ⟨hu,he⟩ := h.cat_dom w hw
    have hs : pr q S ≤α := by
      have hμ := (le_min_iff.mp hC).1
      have : 0≤num (C×Bool) := Nat.cast_nonneg _
      exact hL.trans (by nlinarith only [this,hk,hα,hμ,
        mul_le_mul_of_nonneg_left hα (mul_nonneg this hk.le)])
    exact (pr_mono_left he S).trans (hB S hs)
  have h2 : pr v S ≤ ε := by
    have hh := (pr_cap (bucket_upper w ht q hq f δ hδ hz) S).trans
      (mul_le_mul_of_nonneg_left hL (inv_pos_of_pos hδ).le)
    exact hh.trans ((le_of_eq (by field_simp)).trans (le_min_iff.mp hC).2)
  have h3 : 2*ε < pr w Q-pr v Q := by
    have he := pr_ref_delta w ht.nz P Q
    have hr' := pr_ref_delta v hv Q P
    have heq : (fun i=>¬(Q i↔P i))=S := funext fun i => propext (by unfold S; tauto)
    rw [heq] at hr'
    change 8*ε < varOne w v at hr
    rw [hh] at hr; change pr w P≤pr w Q+pr w S at he
    linarith only [hr,h1,h2,he,hr']
  have he := quadratic_event_progress h w hw F Prod.fst (fun i : C×Bool => i.2=true)
  rw [←hF] at he
  change (pr w Q-pr v Q)^2 ≤ quadraticBudget μ p F-quadraticBudget μ p f at he
  nlinarith only [he,hε,h3]

set_option maxHeartbeats 800000 in
theorem quadratic_ample_thresh (V ε α : ℝ) (hε : 0<ε) (hα : 0<α) :
    ∃ (r : ℕ) (δ : ℝ),0<δ ∧ ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty B]
      (μ : Wgt A) (p : A→ Wgt B), Ultra μ p →
      (∀ S : B→Prop, pr unif S≤α → pr (mixW μ p) S≤ε/8) →
      quadraticTariffs μ p r δ V → ample μ p r ε := by
  classical
  let c := ε/8
  have hc : 0<c := by positivity
  obtain ⟨D,hD⟩ := exists_nat_gt (max 0 (V/c^2))
  have hd := (max_lt_iff.mp hD).2
  rw [div_lt_iff₀ (by positivity)] at hd
  let r := 2^(D+1)
  have h0 : 0<(r:ℝ) := by unfold r; positivity
  let k := min (min α c/r) (1/2)
  have hk : 0<k := lt_min (div_pos (lt_min hα hc) h0) (by norm_num)
  have hk0 : k≤1/2 := min_le_right ..
  have hk' : k≤1 := le_trans hk0 (by norm_num)
  let δ := min α (k^D)
  have hδ : 0<δ := lt_min hα (pow_pos hk D)
  refine ⟨r,δ,hδ,fun A B _ _ _ μ p hw ht hV => ?_⟩
  let e : Wgt B := unif
  have he : IsLaw e := unif_law
  by_contra h
  have hr2 : 2≤r := by
    unfold r; rw [pow_succ]
    have : 0<2^D := by positivity
    omega
  have hstep (n : ℕ) (hn : n≤ D) :
      ∃ f : B → Fin (2^n), stamina (mapW e f) (k^n) ∧
        ↑n*c^2 ≤ quadraticBudget μ p f := by
    induction n with
    | zero =>
      let f := fun _ : B => (0 : Fin (2^0))
      refine ⟨f,?_,by simpa using quadratic_nonneg hw f⟩
      intro i hi
      have hi : i = 0 := by
        have hh := i.isLt; norm_num at hh
        exact Fin.ext (by simp only [Fin.val_zero]; omega)
      subst i; change 1 ≤ pr e (fun x => f x=0)
      simp [f,he.total]
    | succ i ih =>
      obtain ⟨f,hf,hB⟩ := ih (by omega)
      let t := 2^i
      have he' : ∃ w,catalog μ p w ∧ 8*c<varOne w (bucket unif f w) := by
        by_contra! hh
        apply h; refine ⟨t,Nat.pow_le_pow_right (by decide) (by omega),f,?_⟩
        rwa [show 8*c=ε by unfold c; ring] at hh
      obtain ⟨w,hw',hwv⟩ := he'
      have hz : num (Fin t × Bool)*k ≤ min α c := by
        have h1 : Fintype.card (Fin t × Bool) ≤ r :=
          calc _ = 2^(i+1) := by simp [pow_succ,t]
               _ ≤ r := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 := min_le_left (min α c/r) (1/2)
        change k ≤ min α c/r at h2
        rw [le_div_iff₀ h0,mul_comm k] at h2
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast h1) hk.le).trans h2
      obtain ⟨F,hF',hF⟩ := quadratic_divide_progress hw c (k^i) α k hc hk (by linarith)
        (pow_pos hk _) (pow_le_one₀ hk.le hk') ht f hf hz w hw' hwv
      let E : (Fin t×Bool)≃ Fin (2^(i+1)) := Fintype.equivFinOfCardEq (by simp [pow_succ,t])
      refine ⟨E ∘ F,?_,?_⟩
      · rw [←map_nested,pow_succ' k]; exact stamina_equiv _ E _ hF'
      rw [quadratic_equiv,Nat.cast_add,Nat.cast_one]; linarith only [hF,hB]
  obtain ⟨f,hf,hf'⟩ := hstep D le_rfl
  have he' : stamina (mapW unif f) δ := fun i hi => (min_le_right ..).trans (hf i hi)
  have hz := hV _ (f:=f) (by simp; unfold r; rw [pow_succ]; omega) he'
  exact (not_lt_of_ge (le_trans hf' hz)) hd
end
end Lax793645Proofs.Simplifications
