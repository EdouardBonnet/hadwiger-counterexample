import Lax793645Proofs.Simplifications.BlockIndependence
import Lax793645Proofs.Simplifications.HistogramClipping
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.UnfilteredHistogramEnergy

/-! Direct repeated-hit bounds for the actual query program. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Filter Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] {n N l : ℕ}

def queryZ (p : Shape) (x : Inputs p n I) : Mat (Fin n) I :=
  fun u i => freePart p (x i) u

theorem queryZ_uniform (x : I → Wgt (Knobs p.g n))
    (hz : ∀ i, mapW (x i) (freePart p) = unif) :
    mapW (prodW x) (queryZ p) = unif := by
  classical
  let X (z : Inputs p n I) : I → Vec (Fin n) := fun i => freePart p (z i)
  have he := mapW_repeat x (f := fun _ => freePart p (n:=n))
  simp_rw [hz] at he
  have hh : mapW (prodW x) X = unif := he.trans (Eq.symm draws_unif)
  let E : (I → Vec (Fin n)) ≃ Mat (Fin n) I :=
    { toFun := fun z u i => z i u
      invFun := fun z i u => z u i
      left_inv _ := rfl
      right_inv _ := rfl }
  change mapW _ (E ∘ X) = _
  rw [←mapW_nested, hh, unif_equiv]

theorem query_hits_free (v : Template p I)
    (x : I → Wgt (Knobs p.g n)) (hx : ∀ i, IsLaw (x i))
    (hz : ∀ i, mapW (x i) (freePart p) = unif)
    (P : Inputs p n I → Prop) (hp : 0 < pr (prodW x) P)
    (hs : bp (num J*num I-n) ≤ pr (prodW x) P/2) :
    (pr (prodW x) P)^Fintype.card J/2 ≤
      pr (draws J (prodW x)) (fun z => (∀ j, P (z j)) ∧ (v.doubleP n).free z) := by
  have hh := hit_and_independence_lower (J:=J) (prodW x) (prodW_law hx)
    (queryZ p) (queryZ_uniform x hz) P hp (by simpa [num] using hs)
  refine hh.trans (pr_mono (draws_law (prodW_law hx)).nz ?_)
  intro z hz
  have hb : bloom p z := hz.2
  exact ⟨hz.1, v.queries_bloom z _ hb v.glob_inj, v.queries_bloom z _ hb v.glob_inj⟩

theorem fixed_batch_hits (v : Template p I) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (u : ℝ) (hu : 0≤u)
    (hframe : ∀ i : Ports p,
      2*num (Port (tied (globPort p v.t v.aim) (Fin l)) i)-N ≤ -1)
    (hpeak : peakExpense (Fin l) (KeySlots p v.t) 1+ (-(N:ℝ)/2+2*u) ≤0)
    (A : Keys (p:=p) v.t N → Prop) (hA : bp (-u) ≤ pr unif A)
    (z : Fin l → Inputs p n I) (hz : (v.doubleP n).free z) :
    pr (pairW (raw m N) (raw m N)) (fun o => ∀ j, A (v.resultKey o (z j))) ≤
      ((4:ℝ)^Fintype.card (Ports p) * bp (num (Fin l)*num (KeySlots p v.t)^2) *
        (num (Fin l × KeySlots p v.t)+1)) * (pr unif A)^l := by
  classical
  let g := globPort p v.t v.aim
  let s := v.doubleP n
  let Λ := tied g (Fin l)
  let P (_ : Fin l) (r : Rack (KeySlots p v.t) N) := A ((scatter v.t N).symm r)
  have ht (j : Fin l) : pr unif (P j)=pr unif A := by
    rw [show pr unif (P j) = pr (mapW unif (scatter v.t N).symm) A from
      (mapW_pr unif (scatter v.t N).symm A).symm, unif_equiv]
  let B := pooled (s.left ∘ z)
  let Z := database m B B
  have hL := many_frames (N:=N) Λ Z hframe u hu P (fun j => (ht j).symm ▸ hA) hpeak
  let K (o : Forum p n N (Ports p)) := peekR p Λ B B o
  have hk : mapW (pairW (raw m N) (raw m N)) (K ∘ mergeR p)=rackStation Z N := by
    rw [←mapW_nested, law_mergeR]; exact law_peekR m hN hz.1 hz.2
  have he (o : UnitType p n N) :
      (∀ j, P j (led j (K (mergeR p o)))) ↔ ∀ j, A (v.resultKey o (z j)) := by
    unfold K Λ P B
    simp_rw [peek_pooled, Function.comp_apply]
    have ht (j : Fin l) : peekR p g (s.left (z j)) (s.left (z j)) (mergeR p o)=
        scatter v.t N (v.resultKey o (z j)) := v.double_show _ _
    simp_rw [ht, Equiv.symm_apply_apply]
  rw [←hk, mapW_pr] at hL
  simp_rw [Function.comp_apply, he, ht] at hL
  simpa [pow_two, mul_assoc] using hL

theorem averaged_free_hits (v : Template p I) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (u E C : ℝ) (hu : 0≤u)
    (hframe : ∀ i : Ports p,
      2*num (Port (tied (globPort p v.t v.aim) (Fin l)) i)-N ≤ -1)
    (hpeak : peakExpense (Fin l) (KeySlots p v.t) 1+ (-(N:ℝ)/2+2*u) ≤0)
    (hcap : bp (C*N)*((4:ℝ)^Fintype.card (Ports p) *
      bp (num (Fin l)*num (KeySlots p v.t)^2) *
      (num (Fin l × KeySlots p v.t)+1)) ≤ bp (E*l))
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (hh : ∀ i,w i≤bp (C*N)*pairW (raw m N) (raw m N) i)
    (x : I → Wgt (Knobs p.g n)) (hx : ∀ i, IsLaw (x i))
    (A : Keys (p:=p) v.t N → Prop) (hA : bp (-u) ≤ pr unif A) :
    avg w (fun o => pr (draws (Fin l) (prodW x))
      (fun z => (∀ j, A (v.resultKey o (z j))) ∧ (v.doubleP n).free z)) ≤
      bp (E*l)*(pr unif A)^l := by
  classical
  unfold pr
  rw [avg_avg]
  apply (draws_law (prodW_law hx)).avg_le
  intro z
  by_cases hz : (v.doubleP n).free z
  · simp only [hz, and_true]
    have h := (pr_cap hh (fun o => ∀ j, A (v.resultKey o (z j)))).trans
      (mul_le_mul_of_nonneg_left (fixed_batch_hits v m hN u hu hframe hpeak A hA z hz)
        (bp_pos _).le)
    have h' := mul_le_mul_of_nonneg_right hcap
      (pow_nonneg (pr_nonneg unif_law.nz (p:=A)) l)
    rw [mul_assoc] at h'
    exact h.trans h'
  · simp only [hz, and_false, ind_false, avg_zero]
    exact mul_nonneg (bp_pos _).le (pow_nonneg (pr_nonneg unif_law.nz) _)

/-- The lower hit estimate and the Fourier upper estimate give a tail bound
for actual orientation-wise query probabilities. -/
theorem actual_hit_tail (v : Template p I) (m : Mixer p n)
    (hN : 2*num (Full p n)<N) (u E C B : ℝ) (hu : 0≤u) (hB : 0<B)
    (hframe : ∀ i : Ports p,
      2*num (Port (tied (globPort p v.t v.aim) (Fin l)) i)-N ≤ -1)
    (hpeak : peakExpense (Fin l) (KeySlots p v.t) 1+ (-(N:ℝ)/2+2*u) ≤0)
    (hcap : bp (C*N)*((4:ℝ)^Fintype.card (Ports p) *
      bp (num (Fin l)*num (KeySlots p v.t)^2) *
      (num (Fin l × KeySlots p v.t)+1)) ≤ bp (E*l))
    (w : Wgt (UnitType p n N)) (hw : IsLaw w)
    (hh : ∀ i,w i≤bp (C*N)*pairW (raw m N) (raw m N) i)
    (x : I → Wgt (Knobs p.g n)) (hx : ∀ i, IsLaw (x i))
    (hz : ∀ i, mapW (x i) (freePart p)=unif)
    (A : Keys (p:=p) v.t N → Prop) (hA : bp (-u) ≤ pr unif A)
    (hnom : bp (num (Fin l)*num I-n) ≤ B*pr unif A/2) :
    pr w (fun o => B*pr unif A < pr (v.heatMap o x) A) ≤ 2*bp (E*l)/B^l := by
  classical
  let t := pr unif A
  have ht : 0<t := (bp_pos _).trans_le hA
  let H (o : UnitType p n N) := pr (draws (Fin l) (prodW x))
    (fun z => (∀ j, A (v.resultKey o (z j))) ∧ (v.doubleP n).free z)
  let bad (o : UnitType p n N) := B*t < pr (v.heatMap o x) A
  have he o : pr (v.heatMap o x) A = pr (prodW x) (fun z => A (v.resultKey o z)) :=
    mapW_pr _ _ _
  have hlo : pr w bad * ((B*t)^l/2) ≤ avg w H := by
    rw [pr, ←avg_mul]
    apply avg_mono hw.nz
    intro o
    by_cases ho : bad o
    · rw [ind_one ho, one_mul]
      have hp : B*t < pr (prodW x) (fun z => A (v.resultKey o z)) := (he o) ▸ ho
      have hs := query_hits_free (J:=Fin l) v x hx hz (fun z => A (v.resultKey o z))
        ((mul_pos hB ht).trans hp) (hnom.trans (by linarith))
      exact (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_pos hB ht).le hp.le l) (by norm_num)).trans (by simpa using hs)
    · rw [ind_zero ho, zero_mul]; exact pr_nonneg (draws_law (prodW_law hx)).nz
  have hup := averaged_free_hits v m hN u E C hu hframe hpeak hcap w hw hh x hx A hA
  have hp : 0<(B*t)^l/2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hp).mp
  calc pr w bad * ((B*t)^l/2) ≤ bp (E*l)*t^l := hlo.trans hup
       _ = (2*bp (E*l)/B^l)*((B*t)^l/2) := by
         rw [mul_pow]; field_simp

end
end Lax793645Proofs.Simplifications
