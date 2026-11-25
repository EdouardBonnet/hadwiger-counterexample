import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectionNets

/-! Quadratic partition energy for finite families of conditional laws. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
noncomputable section
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def uniformDensity (p : Wgt B) : Wgt B := fun b => p b/unif b
def quadraticBudget (μ : Wgt A) (p : A → Wgt B) (f : B→C) :=
  avg μ (fun i => ode unif (banner unif f (uniformDensity (p i))))
def quadraticTariffs (μ : Wgt A) (p : A→Wgt B) (r : ℕ) (δ V : ℝ) :=
  ∀ (C : Type) [Fintype C], Fintype.card C≤r →
    ∀ (f : B→C), stamina (mapW unif f) δ → quadraticBudget μ p f≤V

theorem uniform_density_restore [Nonempty B] (p : Wgt B) :
    (fun b => unif b*uniformDensity p b)=p := by
  funext b
  have hb : unif (α:=B) b≠0 := by rw [unif_apply]; positivity
  unfold uniformDensity
  field_simp

theorem density_dip [Nonempty B] (p h : Wgt B) :
    dip unif (uniformDensity p) h=avg p h := by
  unfold dip avg
  simp_rw [←mul_assoc]
  simp_rw [show ∀ b, unif b*uniformDensity p b=p b from
    fun b => congr_fun (uniform_density_restore p) b]

theorem projected_density_restore [Nonempty B] (p : Wgt B) (f : B→C) :
    (fun b => unif b*banner unif f (uniformDensity p) b)=bucket unif f p := by
  unfold banner cashbook
  rw [uniform_density_restore]
  rfl

theorem quadratic_cells [Nonempty B] (p : Wgt B) (f : B→C) :
    ode unif (banner unif f (uniformDensity p)) =
      ∑ c, (mapW p f c)^2/mapW unif f c := by
  classical
  unfold ode dip banner cashbook
  rw [uniform_density_restore]
  change avg unif (fun b => (mapW p f (f b)/mapW unif f (f b)) *
    (mapW p f (f b)/mapW unif f (f b))) = _
  simp_rw [←pow_two]
  rw [←mapW_avg unif f (fun c => (mapW p f c/mapW unif f c)^2)]
  unfold avg
  apply sum_congr rfl
  intro c _
  by_cases hc : mapW unif f c=0
  · simp [hc]
  · field_simp

theorem quadratic_nonneg [Nonempty B] {μ : Wgt A} {p : A→Wgt B}
    (h : Ultra μ p) (f : B→C) : 0≤quadraticBudget μ p f :=
  avg_nonneg h.law.nz (fun _ => ode_nonneg unif_law.nz _)

theorem quadratic_equiv [Nonempty B] (μ : Wgt A) (p : A→Wgt B)
    (f : B→C) (e : C≃D) : quadraticBudget μ p (e∘f)=quadraticBudget μ p f := by
  unfold quadraticBudget
  apply avg_congr
  intro i _
  rw [quadratic_cells,quadratic_cells]
  simp_rw [←map_nested,mapW_equiv_val]
  exact e.symm.sum_comp (fun c : C => (mapW (p i) f c)^2/mapW unif f c)

theorem quadratic_tariffs_mono {μ : Wgt A} {p : A→Wgt B}
    {r s : ℕ} {a b V : ℝ} (h : quadraticTariffs μ p r a V)
    (hrs : s≤r) (hb : a≤b) : quadraticTariffs μ p s b V :=
  fun C _ hC f hf => h C (hC.trans hrs) f (fun _ hi => hb.trans (hf _ hi))

/-- An event visible after refinement has squared discrepancy bounded by the
quadratic energy gain. Cauchy--Schwarz replaces the information inequality. -/
theorem quadratic_event_progress [Nonempty B] {μ : Wgt A} {p : A→Wgt B}
    (h : Ultra μ p) (w : Wgt B) (hw : catalog μ p w)
    (f : B→C) (g : C→D) (P : C→Prop) :
    (pr w (P∘f)-pr (bucket unif (g∘f) w) (P∘f))^2 ≤
      quadraticBudget μ p f-quadraticBudget μ p (g∘f) := by
  classical
  let Z i := dip unif (fun b => uniformDensity (p i) b -
    banner unif (g∘f) (uniformDensity (p i)) b) ((fun c => ind (P c))∘f)
  have hz i : Z i^2 ≤ ode unif (banner unif f (uniformDensity (p i)))-
      ode unif (banner unif (g∘f) (uniformDensity (p i))) :=
    archive_gain unif_law.sub _ f g (fun c => ind (P c))
      (fun b => by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _)
  have he i : Z i=pr (p i) (P∘f)-pr (bucket unif (g∘f) (p i)) (P∘f) := by
    unfold Z
    rw [dip_sub,density_dip]
    congr 1
    unfold dip pr avg
    simp_rw [←mul_assoc]
    simp_rw [show ∀ b, unif b*banner unif (g∘f) (uniformDensity (p i)) b=
      bucket unif (g∘f) (p i) b from fun b => congr_fun (projected_density_restore (p i) (g∘f)) b]
    rfl
  obtain ⟨t,ht,htμ,rfl⟩ := hw
  have ht1 : tot t≤1 := (sum_le_sum fun i _ => htμ i).trans_eq h.law.total
  have he' : pr (mixW t p) (P∘f)-pr (bucket unif (g∘f) (mixW t p)) (P∘f)=avg t Z := by
    rw [bucket_mix]
    simp only [pr,mixW_avg,←avg_sub]
    exact avg_congr fun i _ => (he i).symm
  rw [he']
  have hcs := avg_CS ht Z (fun _ => 1)
  simp only [mul_one,one_pow,avg_const,mul_one] at hcs
  have hle := mul_le_mul_of_nonneg_left ht1 (avg_nonneg ht (fun i => sq_nonneg (Z i)))
  rw [mul_one] at hle
  have hmu : avg t (fun i => Z i^2)≤avg μ (fun i => Z i^2) :=
    avg_mono_left (fun i => sq_nonneg _) htμ
  have hgain := avg_mono h.law.nz hz
  rw [avg_sub] at hgain
  exact hcs.trans (hle.trans (hmu.trans hgain))

end
end Lax793645Proofs.Simplifications
