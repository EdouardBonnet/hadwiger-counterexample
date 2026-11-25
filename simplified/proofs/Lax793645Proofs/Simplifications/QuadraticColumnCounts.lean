import Lax793645Proofs.Simplifications.RelativeQuadraticKernel
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function
noncomputable section

variable {D V : Type} [AddCommGroup D] [Module F D] [AddCommGroup V] [Module F V]
  [Fintype D] [Fintype V]

private lemma translated_quadratic_sum (q : QuadraticForm F V) (t : V) :
    avg unif (fun v => wsign (q v) * wsign (q.polarBilin v t)) =
      (avg unif (fun v => wsign (q v))) * wsign (q t) := by
  let E : V ≃ V := ⟨(· + t), (· + t), add_polar t, add_polar t⟩
  have h := avg_bij E unif (fun v => wsign (q v))
  change avg unif (fun v => wsign (q (v+t))) = avg unif (fun v => wsign (q v)) at h
  have hbit (v : V) : q v + q.polarBilin v t = q (v+t) + q t := by
    rw [QuadraticMap.map_add q, ← QuadraticMap.polarBilin_apply_apply]
    linear_combination -(ZModModule.add_self (q t))
  simp_rw [← wsign_add, hbit, wsign_add]
  rw [avg_mul, h]

/-- The signed mass of a polar fiber follows by translating a single
quadratic character. Its dependence on the frame is through its Gram data. -/
theorem quadratic_column_signed_mass (q : QuadraticForm F V)
    (P : D →ₗ[F] V) (b : Module.Dual F D) :
    avg unif (fun v => ind ((q.polarBilin v).comp P = b) * wsign (q v)) =
      (avg unif (fun v => wsign (q v))) * avg unif (fun t => wsign (q (P t) + b t)) := by
  have expand (a : Module.Dual F D) :
      ind (a = b) = avg unif (fun t => wsign (a t) * wsign (b t)) := by
    have hh := wsign_lin (a+b)
    rw [show a+b=0 ↔ a=b by rw [← ZModModule.sub_eq_add, sub_eq_zero]] at hh
    simpa only [LinearMap.add_apply, wsign_add] using hh.symm
  conv_lhs => simp only [expand, ← avg_mul]
  rw [avg_avg]
  have step (t : D) :
      avg unif (fun v => wsign (((q.polarBilin v).comp P) t) * wsign (b t) * wsign (q v)) =
        (avg unif (fun v => wsign (q v))) * wsign (q (P t) + b t) := by
    simp only [LinearMap.comp_apply, wsign_add]
    simp_rw [show ∀ v : V, wsign (q.polarBilin v (P t)) * wsign (b t) * wsign (q v) =
        wsign (q v) * wsign (q.polarBilin v (P t)) * wsign (b t) by intro; ring]
    rw [avg_mul, translated_quadratic_sum, mul_assoc]
  simp_rw [step]
  exact avg_mul' _ _ _

private lemma bit_indicator (x a : F) : ind (x=a) = (1 + wsign x * wsign a)/2 := by
  rcases bit_cases x with rfl|rfl <;> rcases bit_cases a with rfl|rfl <;> norm_num [ind,wsign]

/-- Exact probability of a prescribed new column, including dependent
candidates. The formula applies to every size of the previous frame. -/
theorem quadratic_column_mass [FiniteDimensional F V] [FiniteDimensional F D]
    (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate)
    (P : D →ₗ[F] V) (hP : Injective P) (b : Module.Dual F D) (a : F) :
    pr unif (fun v => (q.polarBilin v).comp P = b ∧ q v = a) =
      (bp (-(dim D : ℝ)) + wsign a * ((avg unif (fun v => wsign (q v))) *
        avg unif (fun t => wsign (q (P t) + b t))))/2 := by
  classical
  let _ : Fintype (Module.Dual F D) := Fintype.ofInjective (fun f => (f : D → F)) DFunLike.coe_injective
  let L := P.dualMap.comp q.polarBilin
  have hs : Surjective L := (dualMap_surjective_of_injective hP).comp
    (LinearMap.BilinForm.toDual q.polarBilin hnd).surjective
  have hlin : pr unif (fun v => (q.polarBilin v).comp P = b) = bp (-(dim D : ℝ)) := by
    change mapW unif L b = _
    rw [map_unif_surjective _ hs, unif_apply, card_space, bp_neg]
    rw [dim, Subspace.dual_finrank_eq]
  unfold pr
  simp only [ind_and, bit_indicator]
  have split (v : V) : ind ((q.polarBilin v).comp P=b) * ((1+wsign (q v)*wsign a)/2) =
      (ind ((q.polarBilin v).comp P=b) + wsign a*(ind ((q.polarBilin v).comp P=b)*wsign (q v)))/2 := by ring
  simp_rw [split]
  rw [avg_div, avg_add, avg_mul', quadratic_column_signed_mass]
  change (pr unif _ + _)/2 = _
  rw [hlin]

/-- For the identity frame, the zero polar fiber consists of the origin.
The same signed count therefore gives the square of the ambient Gauss sum. -/
theorem quadratic_gauss_abs (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate) :
    |avg unif (fun v => wsign (q v))| ≤ bp (-(dim V : ℝ)/2) := by
  have h := quadratic_column_signed_mass q LinearMap.id 0
  have hz (v : V) : (q.polarBilin v).comp LinearMap.id = 0 ↔ v = 0 := by
    rw [LinearMap.comp_id]
    exact ⟨fun hv => (ker_eq_bot.mp (LinearMap.BilinForm.Nondegenerate.ker_eq_bot hnd)) (hv.trans (map_zero _).symm), fun hv => hv ▸ map_zero _⟩
  have point (v : V) : ind ((q.polarBilin v).comp LinearMap.id = 0) * wsign (q v) =
      ind (v=0) := by
    rw [hz]
    by_cases hv : v=0 <;> simp [hv,ind_zero]
  simp only [point, LinearMap.id_apply, LinearMap.zero_apply, add_zero, ← pow_two] at h
  apply half_power
  rw [← h]
  change pr unif (fun v : V => v=0) ≤ _
  rw [pr_point', unif_apply, card_space, bp_neg]

/-- With four spare dimensions beyond twice the span, the count for either
quadratic value exceeds the size of the whole previous span. -/
theorem quadratic_column_exists [FiniteDimensional F V]
    (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate)
    (S : Submodule F V) (b : Module.Dual F S) (a : F)
    (hroom : 2 * finrank F S + 4 ≤ finrank F V) :
    ∃ v ∉ S, q v = a ∧ ∀ s : S, q.polarBilin s v = b s := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let t := bp (-(dim S : ℝ))
  have ht : 0 < t := bp_pos _
  have hdim : 2 * (dim S : ℝ) + 4 ≤ (dim V : ℝ) := by exact_mod_cast hroom
  have hfour : bp 2 = 4 := by norm_num [bp]
  have hshift : bp (-(dim S : ℝ)-2) = t/4 := by rw [bp_sub,hfour]
  have hgauss : |avg unif (fun v => wsign (q v))| ≤ t/4 :=
    (quadratic_gauss_abs q hnd).trans ((bp_le (by linarith only [hdim])).trans_eq hshift)
  have hsigned : |wsign a * ((avg unif (fun v => wsign (q v))) *
      avg unif (fun s : S => wsign (q s + b s)))| ≤ t/4 := by
    have hs := abs_avg_le (f:=fun s : S => wsign (q s + b s)) unif_law.nz
    simp only [wsign_abs, unif_law.avg_const] at hs
    rw [abs_mul, wsign_abs, one_mul, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans hgauss
  let fits (v : V) := (q.polarBilin v).comp S.subtype = b ∧ q v = a
  have hf : t/4 < pr unif fits := by
    change t/4 < pr unif (fun v => (q.polarBilin v).comp S.subtype = b ∧ q v = a)
    rw [quadratic_column_mass q hnd S.subtype S.injective_subtype]
    change t/4 < (t + wsign a * ((avg unif (fun v => wsign (q v))) *
      avg unif (fun s : S => wsign (q s + b s))))/2
    linarith only [(abs_le.mp hsigned).1, ht]
  have hs : pr unif (fun v : V => v ∈ S) ≤ t/4 := by
    rw [pr_unif, nbr_eq_card, card_space, card_space, ← bp_sub, ← hshift]
    apply bp_le
    linarith only [hdim]
  by_contra! hn
  apply (not_le.mpr hf)
  refine (pr_mono unif_law.nz (fun v hv => ?_)).trans hs
  by_contra hvS
  obtain ⟨hb,ha⟩ := hv
  obtain ⟨s,hbad⟩ := hn v hvS ha
  apply hbad
  exact (show q.polarBilin s v = q.polarBilin v s by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]).trans
    (LinearMap.congr_fun hb s)

/-- The candidates already in the span match under the given frame map.
Subtracting them from the full fiber counts preserves equality. -/
theorem quadratic_column_partner [FiniteDimensional F V] [FiniteDimensional F D]
    (q : QuadraticForm F V) (hnd : q.polarBilin.Nondegenerate)
    (P Q : D →ₗ[F] V) (hP : Injective P) (hQ : Injective Q)
    (hform : ∀ d, q (P d) = q (Q d)) (x : V) (hx : x ∉ P.range) :
    ∃ y ∉ Q.range, q y = q x ∧ (q.polarBilin y).comp Q = (q.polarBilin x).comp P := by
  classical
  let b := (q.polarBilin x).comp P
  let fits (T : D →ₗ[F] V) (y : V) := (q.polarBilin y).comp T = b ∧ q y = q x
  let candidates (T : D →ₗ[F] V) := Finset.univ.filter (fits T)
  let old (T : D →ₗ[F] V) := Finset.univ.image (fun d => T d)
  have eqMass : pr unif (fits P) = pr unif (fits Q) := by
    dsimp only [fits]
    rw [quadratic_column_mass q hnd P hP, quadratic_column_mass q hnd Q hQ]
    simp_rw [hform]
  have cardFormula (T : D →ₗ[F] V) :
      pr unif (fits T) = ((candidates T).card : ℝ) / Fintype.card V := by
    rw [pr_unif, nbr_eq_card, Fintype.card_subtype]
  have total : (candidates P).card = (candidates Q).card := by
    rw [cardFormula, cardFormula, div_left_inj' (by exact_mod_cast Fintype.card_ne_zero)] at eqMass
    exact_mod_cast eqMass
  have oldCard (T : D →ₗ[F] V) (hT : Injective T) :
      (candidates T ∩ old T).card = (Finset.univ.filter (fun d => fits T (T d))).card := by
    have he : candidates T ∩ old T = (old T).filter (fits T) := by
      ext y
      simp [candidates, and_comm]
    rw [he]
    change ((Finset.univ.image T).filter (fits T)).card = _
    rw [Finset.filter_image, Finset.card_image_of_injective _ hT]
  have same (d : D) : fits P (P d) = fits Q (Q d) := by
    have hp : (q.polarBilin (P d)).comp P = (q.polarBilin (Q d)).comp Q := by
      ext t
      simp only [LinearMap.comp_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar, ← map_add, hform]
    simp only [fits, hp, hform]
  have inside : (candidates P ∩ old P).card = (candidates Q ∩ old Q).card := by
    rw [oldCard P hP, oldCard Q hQ]
    simp_rw [same]
  have out (T : D →ₗ[F] V) (y : V) :
      y ∈ candidates T \ old T ↔ fits T y ∧ y ∉ T.range := by
    simp [candidates, old, LinearMap.mem_range]
  have hpos := Finset.card_pos.mpr (Finset.nonempty_def.mpr
    ⟨x, (out P x).mpr ⟨⟨rfl,rfl⟩,hx⟩⟩)
  have hpos' : 0 < (candidates Q \ old Q).card := by
    have hp := Finset.card_sdiff_add_card_inter (candidates P) (old P)
    have hq := Finset.card_sdiff_add_card_inter (candidates Q) (old Q)
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos'
  obtain ⟨⟨hpolar,hval⟩,hy⟩ := (out Q y).mp hy
  exact ⟨y,hy,hval,hpolar⟩

end
end Lax793645Proofs.Simplifications
