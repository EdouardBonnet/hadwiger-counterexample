import Lax793645Proofs.Simplifications.MatchingSampling
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteConditioning
import Mathlib.Analysis.SpecialFunctions.Exp

/-! An alternative graph transfer. A list of matching edges records which
conflict neighborhoods it meets. Samples with the same list can be averaged. -/

namespace Lax793645Proofs.Simplifications.MatchingNeighborhoods
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Lax793645Proofs.Upstream.OAI.HadwigerMatching
open Lax793645Proofs.Simplifications
open scoped BigOperators
noncomputable section

variable {X I S : Type*} [Fintype X] [Fintype I] [Nonempty I] [Fintype S]

def survives {L : ℕ} (C : X → X → Prop) (h : Fin L → X) (x : X) : Prop :=
  ∀ j, ¬ C x (h j)

/-- Sampling matching edges misses a neighborhood of mass above δ with
probability at most exp (−Lδ). Average over the reference law to choose one list. -/
theorem hitting_list (f : I → X) (q : Wgt X) (hq : IsLaw q)
    (C : X → X → Prop) (L : ℕ) (δ : ℝ) :
    ∃ a : Fin L → I, pr q (fun x => survives C (f ∘ a) x ∧
      δ < pr (mapW unif f) (C x)) ≤ Real.exp (-(L:ℝ)*δ) := by
  classical
  let draw := prodW (fun _ : Fin L => (unif : Wgt I))
  have hdraw : IsLaw draw := prodW_law fun _ => unif_law
  let miss (a : Fin L → I) (x : X) :=
    survives C (f ∘ a) x ∧ δ < pr (mapW unif f) (C x)
  have hx (x : X) : pr draw (fun a => miss a x) ≤ Real.exp (-(L:ℝ)*δ) := by
    by_cases heavy : δ < pr (mapW unif f) (C x)
    · simp only [miss, heavy, and_true, survives, Function.comp_apply]
      rw [prodW_pr (fun _ : Fin L => (unif : Wgt I)) (fun _ i => ¬ C x (f i))]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [pr_not, (unif_law (α:=I)).total, ← mapW_pr unif f (C x)]
      have hn := (pr_le_tot (p:=C x) (mapW_law unif_law f).nz).trans_eq
        (mapW_law unif_law f).total
      have h1 : 1 - pr (mapW unif f) (C x) ≤ Real.exp (-δ) := by
        linarith [Real.add_one_le_exp (-δ)]
      calc
        _ ≤ (Real.exp (-δ))^L := pow_le_pow_left₀ (by linarith) h1 L
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    · simp [miss, heavy, (Real.exp_pos _).le]
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : Fin L → I => pr q (miss a)) Finset.univ_nonempty
  refine ⟨a, (hdraw.le_avg (fun u => ha u (Finset.mem_univ _))).trans ?_⟩
  change avg draw (fun u => avg q (fun x => ind (miss u x))) ≤ _
  rw [avg_avg]
  exact hq.avg_le hx

/-- If the expected number of missed heavy neighborhoods is below 1, a
single list meets every heavy neighborhood. The manuscript's scales allow this. -/
theorem hitting_all_neighborhoods [Nonempty X] (f : I → X)
    (C : X → X → Prop) (L : ℕ) (δ : ℝ)
    (hsmall : Real.exp (-(L:ℝ)*δ) < (Fintype.card X : ℝ)⁻¹) :
    ∃ a : Fin L → I, ∀ x, survives C (f ∘ a) x → pr (mapW unif f) (C x) ≤ δ := by
  obtain ⟨a,ha⟩ := hitting_list f unif unif_law C L δ
  refine ⟨a,fun x hx => le_of_not_gt fun hh => ?_⟩
  have h := weight_le_pr (w:=(unif : Wgt X)) unif_law.nz
    (p:=fun y => survives C (f ∘ a) y ∧ δ < pr (mapW unif f) (C y)) (x:=x) ⟨hx,hh⟩
  rw [unif_apply] at h
  exact (h.trans ha).not_gt hsmall

/-- The joint density cap charges precisely the missed reference mass.
The other factor 4 comes from retaining at least a quarter of the mixture. -/
theorem mixture_conflict {π : Wgt S} (hπ : IsLaw π) {q w : Wgt X}
    (hq : IsLaw q) (hw : IsLaw w) (K : S → Wgt X) (hK : ∀ s, IsLaw (K s))
    (C : X → X → Prop) (R : X → Prop) (hsupp : carried w R)
    {D δ tail : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hcap : ∀ x, w x ≤ D*q x) (htrim : ∀ x, w x ≤ 4*mixW π K x)
    (hmiss : ∀ s, π s ≠ 0 → pr q (fun x => R x ∧ δ < pr (K s) (C x)) ≤ tail) :
    pr (pairW w w) (fun z => C z.1 z.2) ≤ 4*(δ+D*tail) := by
  let degree (s : S) (x : X) := pr (K s) (C x)
  have hs (s : S) (hpos : π s ≠ 0) : avg w (degree s) ≤ δ+D*tail := by
    let bad (x : X) := R x ∧ δ < degree s x
    have bound (x : X) :
        w x * degree s x ≤ w x * δ + D * (q x * ind (bad x)) := by
      by_cases hr : R x
      · by_cases hd : δ < degree s x
        · rw [ind_one (show bad x from ⟨hr,hd⟩), mul_one]
          have h1 : degree s x ≤ 1 := (pr_le_tot (hK s).nz).trans_eq (hK s).total
          have := mul_le_mul_of_nonneg_left h1 (hw.nz x)
          linarith [hcap x, mul_nonneg (hw.nz x) hδ]
        · rw [ind_zero (show ¬bad x from fun h => hd h.2), mul_zero, mul_zero, add_zero]
          exact mul_le_mul_of_nonneg_left (le_of_not_gt hd) (hw.nz x)
      · rw [hsupp x hr, zero_mul, zero_mul]
        positivity [hq.nz x, ind_nonneg (bad x)]
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => bound x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    change avg w (degree s) ≤ avg w (fun _ => δ)+D*pr q bad at hsum
    rw [hw.avg_const] at hsum
    exact hsum.trans (add_le_add (le_refl δ) (mul_le_mul_of_nonneg_left (hmiss s hpos) hD))
  have hav : avg π (fun s => avg w (degree s)) ≤ δ+D*tail := by
    classical
    calc
      _ = avg π (fun s => if π s = 0 then δ+D*tail else avg w (degree s)) :=
        avg_congr fun s h => by simp [h]
      _ ≤ _ := hπ.avg_le fun s => by split <;> rename_i h <;> first | exact le_rfl | exact hs s h
  have hd (x : X) : pr w (C x) ≤ 4 * avg π (fun s => degree s x) := by
    calc
      _ ≤ pr (fun y => 4*mixW π K y) (C x) := pr_mono_left htrim _
      _ = 4 * pr (mixW π K) (C x) := by
        simp only [pr, avg, mul_assoc, Finset.mul_sum]
      _ = _ := congrArg (4 * ·) (mixW_avg π K (fun y => ind (C x y)))
  change avg (pairW w w) _ ≤ _
  rw [pairW_avg]
  refine (avg_mono hw.nz hd).trans ?_
  rw [avg_mul', avg_avg]
  exact mul_le_mul_of_nonneg_left hav (by norm_num)

variable {A : Type*} [Fintype A] [Nonempty A]

/-- The same finite transfer theorem and parameters as in the manuscript. -/
theorem matching_certificate_transfer (H : Holes A) {μ : Wgt A} (hμ : IsLaw μ)
    {M D ε : ℝ} (hM : 0 < M) (hD : 0 < D) (hε : 0 < ε)
    (hsat : ∀ w, IsLaw w → pairCaps μ M D w → carried w H.unit →
      ε ≤ pr (pairW w w) (fun z => H.conflict z.1 z.2))
    {L b m k s : ℕ} (_hb : 0 < b) (hk : 0 < k) (hkm : 100*k < m+100) (hs : 4*s ≤ k)
    (hscale : D ≤ (2:ℝ)^b*(ε/32)) (hbudget : 384*(b:ℝ) < (L:ℝ)*ε)
    (herr : ((Fintype.card (A × A):ℝ)+1)^L *
      ((2:ℝ)^m*(8/M)^s+(m:ℝ)^(s+s)*(4/D)^s) < 1/8) :
    ∃ x : Fin m → A, (H.graph x).indepNum ≤ 2 ∧
      (connectedMatchingNumber (H.graph x):ℚ) < (m:ℚ)/100 := by
  classical
  by_contra hn
  have hmatch (x : Fin m → A) :
      ∃ e : Fin k ⊕ Fin k → Fin m, Function.Injective e ∧
        (∀ i, H.unit (x (e (.inl i)),x (e (.inr i)))) ∧
        (∀ i j, ¬H.conflict (x (e (.inl i)),x (e (.inr i)))
          (x (e (.inl j)),x (e (.inr j)))) := by
    have hnot : ¬ (connectedMatchingNumber (H.graph x):ℚ)<(m:ℚ)/100 :=
      fun h => hn ⟨x,H.indepNum_graph_le x,h⟩
    have hr : (m:ℚ) ≤ 100*(connectedMatchingNumber (H.graph x):ℚ) := by linarith
    have hn' : m ≤ 100*connectedMatchingNumber (H.graph x) := by exact_mod_cast hr
    have ht : k ≤ connectedMatchingNumber (H.graph x) := by omega
    obtain ⟨e,he,hu,hc⟩ := H.matching_pairs x
    let f : Fin k → Fin (connectedMatchingNumber (H.graph x)) := Fin.castLE ht
    have hf : Function.Injective f := Fin.castLE_injective ht
    exact ⟨e ∘ Sum.map f f, he.comp (Sum.map_injective.mpr ⟨hf,hf⟩),
      fun i => hu (f i),fun i j => hc (f i) (f j)⟩
  choose e he hu hc using hmatch
  let _ : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let f (x : Fin m → A) (i : Fin k) := (x (e x (.inl i)),x (e x (.inr i)))
  let K (x : Fin m → A) := mapW (unif : Wgt (Fin k)) (f x)
  let π := prodW (fun _ : Fin m => μ)
  have hπ : IsLaw π := prodW_law fun _ => hμ
  have hK x : IsLaw (K x) := mapW_law unif_law (f x)
  let q := pairW μ μ
  have hq : IsLaw q := pairW_law hμ hμ
  let δ := ε/32
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose a ha using fun x => hitting_list (f x) q hq H.conflict L δ
  let code (x : Fin m → A) : Fin L → A × A := f x ∘ a x
  let codes := mapW π code
  obtain ⟨h, _, largest⟩ := Finset.exists_max_image Finset.univ codes Finset.univ_nonempty
  let F (x : Fin m → A) := code x = h
  let count : ℝ := Fintype.card (Fin L → A × A)
  have hcount : 1 ≤ count * pr π F := by
    have hh := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => largest c (Finset.mem_univ _))
    change tot codes ≤ _ at hh
    rw [(mapW_law hπ code).total] at hh
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, count, codes, mapW, F] using hh
  have hcpos : 0 < count := by dsimp [count]; exact_mod_cast Fintype.card_pos
  have hF : 0 < pr π F := by
    by_contra! hz
    linarith [mul_nonpos_of_nonneg_of_nonpos hcpos.le hz]
  let post := onW π F
  have hpost : IsLaw post := normW_law (subW_nonneg hπ.nz F) hF
  have hclass x (hx : post x ≠ 0) : code x = h :=
    Classical.byContradiction fun hf => hx (normW_carried (subW_carried π F) x hf)
  let σ := mixW post K
  have hσ : IsLaw σ := mixW_law hpost hK
  let R := survives H.conflict h
  have hsupport (x : Fin m → A) (hx : post x ≠ 0) : carried (K x) R := by
    apply map_carried
    intro i j
    rw [← hclass x hx]
    exact hc x i (a x j)
  have mix_carried (P : A × A → Prop) (hp : ∀ x, post x ≠ 0 → carried (K x) P) :
      carried σ P := by
    intro z hz
    change avg post (fun x => K x z) = 0
    exact (avg_congr (fun x hx => hp x hx z hz)).trans (avg_zero post)

  let S₀ := heavyEndpoints μ M σ
  let E := heavyPairs μ D σ
  let A₀ := retainedUnits μ M D σ
  let bad (x : Fin m → A) := badS S₀ s x ∨ badE E s x
  let err := (2:ℝ)^m*(8/M)^s+(m:ℝ)^(s+s)*(4/D)^s
  have hbad : pr π bad ≤ err := by
    refine (pr_or_le hπ.nz).trans (((add_le_add (badS_pr hμ S₀ s m)
      (badE_pr hμ E s m))).trans ?_)
    have hS := heavyEndpoints_mass hμ hM hσ
    have hE := heavyPairs_mass (μ:=μ) hD hσ
    have hn₁ := pr_nonneg (p:=S₀) hμ.nz
    have hn₂ := pr_nonneg (p:=E) hq.nz
    dsimp only [err]
    change pr μ S₀ ≤ _ at hS
    change pr (pairW μ μ) E ≤ _ at hE
    gcongr
  have hcnum : count ≤ ((Fintype.card (A × A):ℝ)+1)^L := by
    dsimp only [count]
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    gcongr
    linarith
  have hsmall : pr post bad < 1/8 := by
    have h₁ : count*err < 1/8 :=
      (mul_le_mul_of_nonneg_right hcnum (by dsimp [err]; positivity)).trans_lt herr
    have h₂ : err < (1/8)*pr π F := by
      apply lt_of_mul_lt_mul_left (a:=count) _ hcpos.le
      nlinarith only [h₁,hcount]
    rw [pr_on, div_lt_iff₀ hF]
    exact (pr_mono hπ.nz fun _ h => h.2).trans_lt (hbad.trans_lt h₂)
  have hα : 1/4 ≤ pr σ A₀ := by
    have hret (x : Fin m → A) :
        (1/2)*ind (¬ bad x) ≤ pr (K x) A₀ := by
      by_cases hb : bad x
      · simpa only [ind_zero (not_not_intro hb),mul_zero] using pr_nonneg (p:=A₀) (hK x).nz
      · rw [ind_one hb,mul_one]
        exact matching_retained_mass hk hs x (e x) (he x) S₀ E hb
    have havg := avg_mono hpost.nz hret
    rw [avg_mul'] at havg
    change (1/2)*pr post (fun x => ¬bad x) ≤ _ at havg
    rw [pr_not,hpost.total] at havg
    change 1/4 ≤ avg (mixW post K) _
    rw [mixW_avg]
    change 1/4 ≤ avg post (fun x => pr (K x) A₀)
    linarith only [havg,hsmall]
  let w := onW σ A₀
  have hw : IsLaw w := normW_law (subW_nonneg hσ.nz A₀) (by change 0 < pr σ A₀; linarith)
  have caps := retained_caps hμ hM hD hσ hα
  have inherit (P : A × A → Prop) (hp : carried σ P) : carried w P :=
    normW_carried fun z hz => by rw [subW, hp z hz, zero_mul]
  have hu' := inherit H.unit (mix_carried H.unit fun x _ => map_carried _ (f x) _ (hu x))
  have higher := hsat w hw caps hu'
  have lower := mixture_conflict hpost hq hw K hK H.conflict R
    (inherit R (mix_carried R hsupport)) hD.le hδ.le caps.2.2
    (fun x => by simpa using on_mon hσ.nz (by norm_num : (0:ℝ)<1/4) hα x)
    (fun x hx => by
      have hm := ha x
      change pr q (fun z => survives H.conflict (code x) z ∧ δ < pr (K x) (H.conflict z)) ≤ _ at hm
      rw [hclass x hx] at hm
      exact hm)
  have hroom : (b:ℝ) ≤ (L:ℝ)*δ := by dsimp [δ]; nlinarith
  have hexp : (2:ℝ)^b ≤ Real.exp ((L:ℝ)*δ) := by
    calc
      _ ≤ (Real.exp 1)^b := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) _
      _ = Real.exp (b:ℝ) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := Real.exp_le_exp.mpr hroom
  have htail : D * Real.exp (-(L:ℝ)*δ) ≤ δ := by
    rw [neg_mul,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _),mul_comm]
    exact hscale.trans (mul_le_mul_of_nonneg_right hexp hδ.le)
  change _ ≤ 4*(δ+D*Real.exp (-(L:ℝ)*δ)) at lower
  dsimp only [δ] at *
  linarith

end
end Lax793645Proofs.Simplifications.MatchingNeighborhoods
