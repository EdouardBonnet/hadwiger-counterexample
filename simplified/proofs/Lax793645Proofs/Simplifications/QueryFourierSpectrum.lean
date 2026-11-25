import Lax793645Proofs.Simplifications.LinearReferenceProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]

private def recordRows (S : Finset (Vec I)) : Mat (Fin S.card) I :=
  fun i => ((S.equivFin.symm i : S) : Vec I)

omit [DecidableEq I] in
private theorem recorded_character (S : Finset (Vec I)) {ξ : Vec I} (hξ : ξ ∈ S) :
    ∃ g : Wgt (Vec (Fin S.card)), vectorPhase ξ = g ∘ (recordRows S).mulVec := by
  refine ⟨fun y => wsign (y (S.equivFin ⟨ξ,hξ⟩)), ?_⟩
  funext x
  simp [recordRows, vectorPhase, Matrix.mulVec]

private theorem supported_coefficient (K : Vec I → Prop) (f : Wgt (Vec I))
    (hK : 0 < pr unif K) (ξ : Vec I) :
    linearFourier (fun x => f x * ind (K x)) ξ =
      pr unif K * dip (unifOn K) f (vectorPhase ξ) := by
  rw [dip, ←part_reset K _ hK]
  unfold linearFourier partMean
  apply avg_congr
  intro x _
  ring

/-- Bessel's inequality on a Gram reference set. Only the energy on the
partition recording the specified characters is needed. -/
private theorem recorded_bessel (K : Vec I → Prop) (hK : 0 < pr unif K)
    (d : Wgt (Vec I)) (S : Finset (Vec I)) :
    pr unif K * (∑ ξ ∈ S, (dip (unifOn K) d (vectorPhase ξ))^2) ≤
      ode (unifOn K) (banner (unifOn K) (recordRows S).mulVec d) := by
  let ν := unifOn K
  let P := (recordRows S).mulVec
  let g := banner ν P d
  let u x := g x * ind (K x)
  have he ξ (hξ : ξ ∈ S) :
      linearFourier u ξ = pr unif K * dip ν d (vectorPhase ξ) := by
    rw [supported_coefficient K g hK]
    obtain ⟨a,ha⟩ := recorded_character S hξ
    rw [ha, ←cash_orth ν (unifOn_sub K).nz P d a]
  have hsum := sum_le_univ_sum_of_nonneg (s := S) (fun ξ => sq_nonneg (linearFourier u ξ))
  rw [linear_fourier_parseval] at hsum
  have hright : avg unif (fun x => u x ^ 2) = pr unif K * ode ν g := by
    rw [ode,dip,←part_reset K _ hK]
    apply avg_congr
    intro x _
    by_cases hx : K x <;> simp [u, ind_one, ind_zero, hx, pow_two]
  rw [hright] at hsum
  have hleft : ∑ ξ ∈ S, (linearFourier u ξ)^2 =
      pr unif K * (pr unif K * ∑ ξ ∈ S, (dip ν d (vectorPhase ξ))^2) := by
    rw [←mul_assoc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ξ hξ => by rw [he ξ hξ]; ring
  rw [hleft] at hsum
  exact (mul_le_mul_iff_right₀ hK).mp hsum

/-- A frequency is recorded if any allowed filter can have a large
coefficient there. Parseval bounds the size of this set for the whole leaf. -/
theorem filtered_large_spectrum (K : Vec I → Prop) (hK : 0 < pr unif K)
    (μ : Wgt J) (hμ : SubLaw μ) (d : J → Wgt (Vec I))
    (τ V : ℝ) (hτ : 0 < τ) (R : ℕ) (hR : V < pr unif K * (R * τ^2))
    (henergy : ∀ P : Mat (Fin R) I, densityFamilyEnergy (unifOn K) μ d P.mulVec ≤ V) :
    ∃ S : Finset (Vec I), S.card ≤ R ∧ ∀ t : Wgt J,
      (∀ j, 0 ≤ t j) → (∀ j, t j ≤ μ j) →
      ∀ ξ ∉ S, |dip (unifOn K) (mixW t d) (vectorPhase ξ)| ≤ τ := by
  let ν := unifOn K
  let Z (ξ : Vec I) := avg μ (fun j => (dip ν (d j) (vectorPhase ξ))^2)
  let S := univ.filter fun ξ => τ^2 ≤ Z ξ
  refine ⟨S, ?_, ?_⟩
  · by_contra! hc
    obtain ⟨E,hES,hE⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hc)
    have hlow : (R:ℝ)*τ^2 ≤ ∑ ξ ∈ E, Z ξ := by
      calc
        _ = ∑ _ξ ∈ E, τ^2 := by simp [hE]
        _ ≤ _ := sum_le_sum fun ξ hξ => (mem_filter.mp (hES hξ)).2
    have hu := avg_mono hμ.nz (fun j => recorded_bessel K hK (d j) E)
    rw [avg_mul', avg_sum] at hu
    have he : densityFamilyEnergy ν μ d (recordRows E).mulVec ≤ V := by
      subst R
      exact henergy (recordRows E)
    exact (not_le_of_gt hR) ((mul_le_mul_of_nonneg_left hlow hK.le).trans (hu.trans he))
  intro t ht hcap ξ hξ
  have hZ : Z ξ < τ^2 := lt_of_not_ge (fun h => hξ (mem_filter.mpr ⟨mem_univ _,h⟩))
  let f j := dip ν (d j) (vectorPhase ξ)
  have hcs := avg_CS ht f (fun _ => 1)
  simp only [mul_one,one_pow,avg_const,mul_one] at hcs
  have ht1 : tot t ≤ 1 := (Finset.sum_le_sum fun j _ => hcap j).trans hμ.total
  have hs := (mul_le_mul_of_nonneg_left ht1 (avg_nonneg ht fun j => sq_nonneg (f j))).trans_eq (mul_one _)
  have hh := hcs.trans (hs.trans (avg_mono_left (fun j => sq_nonneg (f j)) hcap))
  rw [dip_density_mixture]
  change |avg t f| ≤ τ
  exact (sq_le_sq₀ (abs_nonneg _) hτ.le).mp (by simpa only [sq_abs] using hh.trans hZ.le)

private theorem large_test_coefficients (u : Wgt (Vec I)) (hu : ∀ x, |u x| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (hk : 1 ≤ k * δ^2) :
    (univ.filter fun ξ => δ < |linearFourier u ξ|).card ≤ k := by
  let E := univ.filter fun ξ => δ < |linearFourier u ξ|
  have h : (E.card : ℝ)*δ^2 ≤ ∑ ξ ∈ E, (linearFourier u ξ)^2 := by
    calc
      _ = ∑ _ξ ∈ E, δ^2 := by simp
      _ ≤ _ := sum_le_sum fun ξ hξ => by
        simpa only [sq_abs] using pow_le_pow_left₀ hδ.le (mem_filter.mp hξ).2.le 2
  have hs := sum_le_univ_sum_of_nonneg (s := E) (fun ξ => sq_nonneg (linearFourier u ξ))
  rw [linear_fourier_parseval] at hs
  have hn : avg unif (fun x => (u x)^2) ≤ 1 := unif_law.avg_le fun x => by
    simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hu x) 2
  exact_mod_cast (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp (h.trans (hs.trans (hn.trans hk)))

/-- For a bounded test, record its large Fourier coefficients once. Project its
zero extension using the uniform ambient law. The resulting bounded test keeps
all recorded coefficients exactly and introduces no new ones. -/
private theorem truncate_test (u : Wgt (Vec I)) (hu : ∀ x, |u x| ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (hk : 1 ≤ k * δ^2) :
    ∃ T : Wgt (Vec I), (∀ x, |T x| ≤ 1) ∧ fourierNorm T ≤ 2^k ∧
      (∀ ξ, |linearFourier u ξ - linearFourier T ξ| ≤ δ) ∧
      (∀ ξ, linearFourier u ξ = 0 → linearFourier T ξ = 0) := by
  let E := univ.filter fun ξ => δ < |linearFourier u ξ|
  let P := recordRows E
  let T := banner unif P.mulVec u
  have hcard := large_test_coefficients u hu δ hδ k hk
  have hb := cashbook_bound unif unif_law.nz P.mulVec u 1 zero_le_one hu
  refine ⟨T,fun x => hb _,?_,?_,?_⟩
  · have h := linear_bounded_fourier_norm P (cashbook unif P.mulVec u) 1 hb
    have hnum : num (Vec (Fin E.card)) = (2:ℝ)^E.card := by simp [num,Vec,F]
    rw [mul_one,hnum] at h
    exact h.trans (pow_le_pow_right₀ (by norm_num) hcard)
  · intro ξ
    by_cases hξ : ξ ∈ E
    · obtain ⟨v,hv⟩ := recorded_character E hξ
      have h := cash_orth unif unif_law.nz P.mulVec u v
      rw [←hv] at h
      have hz : linearFourier T ξ = linearFourier u ξ := by
        simpa only [linearFourier,dip,mul_comm] using h
      rw [hz,sub_self,abs_zero]
      exact hδ.le
    · have hsmall : |linearFourier u ξ| ≤ δ :=
        le_of_not_gt fun h => hξ (mem_filter.mpr ⟨mem_univ _,h⟩)
      dsimp only [T]
      rw [linear_projection_fourier]
      split <;> simp_all [hδ.le]
  · intro ξ h
    dsimp only [T]
    rw [linear_projection_fourier,h,ite_self]

private theorem dip_fourier_expansion (ν f T : Wgt (Vec I)) :
    dip ν f T = ∑ ξ, linearFourier T ξ * dip ν f (vectorPhase ξ) := by
  have he x : f x * T x = ∑ ξ, linearFourier T ξ * (f x * vectorPhase ξ x) := by
    conv_lhs => rhs; rw [←hat_eqn T x]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    unfold linearFourier
    ring
  unfold dip
  simp_rw [he,avg_sum,avg_mul']

/-- Test a filtered density against a function orthogonal to the recorded
characters. The leaf comparison is only applied to one bounded, supported
residual. Its supremum bound is independent of the Fourier cutoff. -/
private theorem centered_spectrum_test (K : Vec I → Prop) (hK : 0 < pr unif K)
    (hν : IsLaw (unifOn K)) (f W : Wgt (Vec I)) (hW : ∀ x, |W x| ≤ 1)
    (S : Finset (Vec I)) (η τ δ γ : ℝ) (hδ : 0 < δ) (hτ : 0 ≤ τ) (hγ : 0 ≤ γ)
    (k : ℕ) (hk : 1 ≤ k * δ^2) (hsmall : γ * 2^k ≤ δ)
    (hbias : ∀ ξ : Vec I, ξ ≠ 0 → |avg (unifOn K) (vectorPhase ξ)| ≤ γ)
    (hcenter : ∀ ξ ∈ S, dip (unifOn K) W (vectorPhase ξ) = 0)
    (htail : ∀ ξ ∉ S, |dip (unifOn K) f (vectorPhase ξ)| ≤ τ)
    (hcompare : ∀ D : Wgt (Vec I), (∀ x, |D x| ≤ 1) → (∀ x, D x ≠ 0 → K x) →
      (∀ ξ, |linearFourier D ξ| ≤ δ) → |dip (unifOn K) f D| ≤ η) :
    pr unif K * |dip (unifOn K) f W| ≤ 2*η + 2^k*τ := by
  let ν := unifOn K
  let a := pr (unif : Wgt (Vec I)) K
  have ha : 0 < a := hK
  have ha1 : a ≤ 1 := (pr_le_tot unif_law.nz).trans_eq unif_law.total
  let u x := W x * ind (K x)
  have hu x : |u x| ≤ 1 := by
    unfold u
    rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
    exact (mul_le_mul (hW x) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)
  obtain ⟨T,hT,hNorm,happrox,hzero⟩ := truncate_test u hu δ hδ k hk
  let D x := (a*W x-T x)*ind (K x)/2
  have hD x : |D x| ≤ 1 := by
    dsimp only [D]
    rw [abs_div,abs_mul,abs_of_nonneg (ind_nonneg _)]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply (div_le_one (by norm_num : (0:ℝ)<2)).mpr
    have hh : |a*W x| ≤ 1 := by
      rw [abs_mul,abs_of_pos ha]
      exact (mul_le_mul ha1 (hW x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact ((mul_le_mul_of_nonneg_left (ind_le_one _) (abs_nonneg _)).trans_eq (mul_one _)).trans
      ((abs_sub _ _).trans (by linarith only [hh,hT x]))
  have hsup x (hx : D x ≠ 0) : K x := by
    by_contra hn
    exact hx (by simp [D,ind_zero hn])
  have hFour ξ : |linearFourier D ξ| ≤ δ := by
    have hb := small_bias_test ν hν γ hγ hbias (fun x => vectorPhase ξ x * T x)
    have hc : fourierNorm (fun x => vectorPhase ξ x * T x) ≤ 2^k :=
      (fourier_norm_mul (vectorPhase ξ) T).trans (by simpa only [fourier_norm_character,one_mul] using hNorm)
    have hdiff : |dip ν T (vectorPhase ξ) - linearFourier T ξ| ≤ δ :=
      (by simpa only [dip,linearFourier,mul_comm] using hb :
        |dip ν T (vectorPhase ξ) - linearFourier T ξ| ≤ _) |>.trans
        ((mul_le_mul_of_nonneg_left hc hγ).trans hsmall)
    have hcoeff : linearFourier D ξ = a * (linearFourier u ξ - dip ν T (vectorPhase ξ)) / 2 := by
      rw [mul_sub, ←supported_coefficient K T hK]
      unfold linearFourier
      rw [←avg_mul',←avg_sub,←avg_div]
      apply avg_congr
      intro x _
      dsimp only [u,D]
      ring
    have hh := abs_sub_le (linearFourier u ξ) (linearFourier T ξ) (dip ν T (vectorPhase ξ))
    rw [hcoeff,abs_div,abs_mul,abs_of_pos ha]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_iff₀ (by norm_num)).mpr
    have hb := mul_le_mul_of_nonneg_right ha1 (abs_nonneg (linearFourier u ξ-dip ν T (vectorPhase ξ)))
    rw [one_mul] at hb
    rw [abs_sub_comm (linearFourier T ξ)] at hh
    linarith only [hb,hh,happrox ξ,hdiff]
  have hDint := hcompare D hD hsup hFour
  have hTint : |dip ν f T| ≤ 2^k*τ := by
    rw [dip_fourier_expansion]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul]
    calc
      _ ≤ ∑ ξ, |linearFourier T ξ| * τ := by
        apply sum_le_sum
        intro ξ _
        by_cases hx : ξ ∈ S
        · have hz : linearFourier u ξ = 0 := by
            rw [supported_coefficient K W hK,hcenter ξ hx,mul_zero]
          rw [hzero ξ hz,abs_zero,zero_mul,zero_mul]
        exact mul_le_mul_of_nonneg_left (htail ξ hx) (abs_nonneg _)
      _ ≤ _ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hNorm hτ
  have hpair : dip ν f D = (a * dip ν f W - dip ν f T)/2 := by
    unfold dip
    rw [←avg_mul',←avg_sub,←avg_div]
    apply avg_congr
    intro x hx
    have hxK : K x := by
      by_contra hn
      exact hx (by simp [ν,unifOn,normW,ind_zero hn])
    dsimp only [D]
    rw [ind_one hxK,mul_one]
    ring
  rw [hpair,abs_div] at hDint
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at hDint
  have hh := abs_sub_le (a*dip ν f W) (dip ν f T) 0
  rw [sub_zero,sub_zero,abs_mul,abs_of_pos ha] at hh
  linarith only [hh,hDint,hTint]

/-- A single set of frequencies controls all subweights, including subweights
chosen after viewing the opposite leaf. The test cutoff and test norm are
chosen before the number of frequencies on this leaf. -/
theorem spectrum_all_filters (K : Vec I → Prop) (hK : 0 < pr unif K)
    (hν : IsLaw (unifOn K)) (μ : Wgt J) (hμ : SubLaw μ) (d : J → Wgt (Vec I))
    (η τ δ γ V ε : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hγ : 0 ≤ γ)
    (k R : ℕ) (hk : 1 ≤ k * δ^2) (hsmall : γ * 2^k ≤ δ)
    (hR : V < pr unif K * (R * τ^2))
    (henergy : ∀ P : Mat (Fin R) I, densityFamilyEnergy (unifOn K) μ d P.mulVec ≤ V)
    (hbias : ∀ ξ : Vec I, ξ ≠ 0 → |avg (unifOn K) (vectorPhase ξ)| ≤ γ)
    (hcompare : ∀ (t : Wgt J), (∀ j, 0 ≤ t j) → (∀ j, t j ≤ μ j) →
      ∀ D : Wgt (Vec I), (∀ x, |D x| ≤ 1) → (∀ x, D x ≠ 0 → K x) →
      (∀ ξ, |linearFourier D ξ| ≤ δ) → |dip (unifOn K) (mixW t d) D| ≤ η)
    (hbudget : 2*(2*η+2^k*τ) ≤ pr unif K * ε) :
    ∃ r : ℕ, r ≤ R ∧ ∃ P : Mat (Fin r) I,
      ∀ t : Wgt J, (∀ j, 0 ≤ t j) → (∀ j, t j ≤ μ j) →
        lcost (unifOn K) (mixW t d) (banner (unifOn K) P.mulVec (mixW t d)) ≤ ε := by
  let ν := unifOn K
  obtain ⟨S,hS,hspec⟩ := filtered_large_spectrum K hK μ hμ d τ V hτ R hR henergy
  let P := recordRows S
  refine ⟨S.card,hS,P,fun t ht hcap => ?_⟩
  let f := mixW t d
  obtain ⟨U,hU,hcost⟩ := bounded_discrepancy_test ν f (banner ν P.mulVec f)
  let W x := (U x - banner ν P.mulVec U x)/2
  have hW x : |W x| ≤ 1 := by
    dsimp only [W]
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply (div_le_one (by norm_num)).mpr
    have hb := cashbook_bound ν hν.nz P.mulVec U 1 zero_le_one hU (P*ᵥx)
    change |banner ν P.mulVec U x| ≤ 1 at hb
    exact (abs_sub _ _).trans (by linarith only [hb,hU x])
  have hcenter ξ (hξ : ξ ∈ S) : dip ν W (vectorPhase ξ) = 0 := by
    obtain ⟨g,hg⟩ := recorded_character S hξ
    rw [hg]
    have hh := cash_orth ν hν.nz P.mulVec U g
    change dip ν W (g ∘ P.mulVec) = 0
    unfold dip at hh ⊢
    dsimp only [W]
    simp_rw [div_mul_eq_mul_div,sub_mul,avg_div,avg_sub,hh,sub_self,zero_div]
  have h := centered_spectrum_test K hK hν f W hW S η τ δ γ hδ hτ.le hγ k hk hsmall
    hbias hcenter (hspec t ht hcap) (hcompare t ht hcap)
  have he : dip ν f W = lcost ν f (banner ν P.mulVec f)/2 := by
    rw [←hcost,dip_sub,projection_self_adjoint ν hν.nz]
    unfold dip
    dsimp only [W]
    simp_rw [mul_div_assoc',mul_sub,avg_div,avg_sub]
  rw [show dip (unifOn K) f W = _ from he] at h
  have hh := (mul_le_mul_of_nonneg_left (le_abs_self _) hK.le).trans h
  exact (le_of_mul_le_mul_left (by linarith only [hh,hbudget] : pr unif K * lcost ν f (banner ν P.mulVec f) ≤ _) hK)

end
end Lax793645Proofs.Simplifications
