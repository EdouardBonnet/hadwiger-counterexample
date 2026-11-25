import Lax793645Proofs.Simplifications.SuccessfulLinearQueries
import Lax793645Proofs.Simplifications.LinearAdaptiveOverlap
import Lax793645Proofs.Simplifications.QueryReferenceBias

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {q : Format} {d : Rates} {b : Bool}

/-- A common finite linear partition preserves successful-query overlap
on average over independent leaves. Both acceptance filters are chosen
after the partition and may depend on both leaves. -/
theorem successful_query_common_projection (w : Quill p q d b)
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hw : w.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ S : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (UnitType p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ a : Λ→Charts p n d,
      let ν:=unifOn (queryReferenceSet (w.pen t) z (M*n))
      let D (l : Λ) (F : UnitType p n (M*n)→Prop):=
        density ν (mapW (w.sales t z (π l) F m (a l)) (queryCoordinateEquiv t (M*n)).symm)
      ∃ s : ℕ,s≤S ∧ ∃ C : Mat (Fin s) (Fin (M*n)×Bool×KeySlots p t),
        ∀ F G : Λ×Λ→UnitType p n (M*n)→Prop,
        avg (pairW μ μ) (fun l=>dip ν (banner ν C.mulVec (D l.1 (F l)))
          (banner ν C.mulVec (D l.2 (G l))))≤
        avg (pairW μ μ) (fun l=>dip ν (D l.1 (F l)) (D l.2 (G l)))+ε := by
  obtain ⟨B₁,hB₁,hinit⟩:=successful_query_linear_partition w t z hw hp M hM c
  obtain ⟨B₂,hB₂,hbound⟩:=successful_linear_density_bound w t z hw hp M hM c
  let B:=max B₁ B₂
  have hB : 0<B:=lt_of_lt_of_le zero_lt_one (hB₁.trans (le_max_left ..))
  let δ:=ε/(16*B)
  let η:=ε/(4*B^2)
  have hδ : 0<δ:=div_pos hε (mul_pos (by norm_num) hB)
  have hη : 0<η:=div_pos hε (mul_pos (by norm_num) (sq_pos_of_pos hB))
  obtain ⟨R,hR⟩:=hinit δ hδ
  obtain ⟨S,hS⟩:=exists_nat_ge ((R:ℝ)*bp R/η)
  let F₀:=B*bp (R:ℝ)
  let γ (n:ℕ):=2*bp (num (crowded (ownPort t)))*bp (-((M*n:ℕ):ℝ)/2)
  obtain ⟨hγ,hνcal⟩:=query_reference_bias_calendar (w.pen t) M hM
  change Tendsto γ atTop (nhds 0) at hγ
  have he : Tendsto (fun n=>γ n*(2*F₀^2+4*B*bp (S:ℝ)*F₀)) atTop (nhds 0):=by
    simpa only [zero_mul] using hγ.mul_const (2*F₀^2+4*B*bp (S:ℝ)*F₀)
  refine ⟨S,?_⟩
  filter_upwards [hR,hbound S,hνcal,he.eventually (eventually_le_nhds (half_pos hε))]
    with n hn hb hνn hsmall m hN Λ _ μ hμ π hπ hcap a ν D
  obtain ⟨hν,hbias⟩:=hνn z
  have hγn : 0≤γ n:=mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le
  choose r hr P hP using fun l=>hn m hN (π l) (hπ l) (hcap l) (a l)
  obtain ⟨s,hs,C,hC⟩:=linear_adaptive_overlap μ hμ r P R hr η hη
  have hsS : s≤S:=by exact_mod_cast hs.trans hS
  refine ⟨s,hsS,C,fun F G=>?_⟩
  let f l:=D l.1 (F l)
  let g l:=D l.2 (G l)
  let φ (l:Λ×Λ):=cashbook ν (P l.1).mulVec (f l)
  let ψ (l:Λ×Λ):=cashbook ν (P l.2).mulVec (g l)
  have hd l H x : 0≤D l H x:=div_nonneg
    (map_nz (w.sales_pos (π l) (a l) t z m H (hπ l).nz) _ _) (hν.nz x)
  have hφ l x : 0≤φ l x ∧ φ l x≤B := by
    have hh:=cashbook_bound_of_banner ν (f l) hν.nz (P l.1).mulVec B₁
      (zero_le_one.trans hB₁) ((hP l.1 (F l)).1) x
    exact ⟨hh.1,hh.2.trans (le_max_left ..)⟩
  have hψ l x : 0≤ψ l x ∧ ψ l x≤B := by
    have hh:=cashbook_bound_of_banner ν (g l) hν.nz (P l.2).mulVec B₁
      (zero_le_one.trans hB₁) ((hP l.2 (G l)).1) x
    exact ⟨hh.1,hh.2.trans (le_max_left ..)⟩
  have hf l : lcost ν (fun x=>φ l (P l.1*ᵥx)) (f l)≤δ:=by
    change lcost ν (banner ν (P l.1).mulVec (f l)) (f l)≤δ
    rw [lcost_symm]
    exact (hP l.1 (F l)).2
  have hg l : lcost ν (fun x=>ψ l (P l.2*ᵥx)) (g l)≤δ:=by
    change lcost ν (banner ν (P l.2).mulVec (g l)) (g l)≤δ
    rw [lcost_symm]
    exact (hP l.2 (G l)).2
  have hproj l H x : 0≤banner ν C.mulVec (D l H) x ∧ banner ν C.mulVec (D l H) x≤B := by
    have hh:=hb m hN (π l) (hπ l) (hcap l) (a l) s hsS C H x
    exact ⟨hh.1,hh.2.trans (le_max_right ..)⟩
  have hh:=hC ν hν (γ n) hγn hbias B δ hB.le hδ.le f g φ ψ
    (fun l=>hd l.1 (F l)) (fun l=>hd l.2 (G l)) hφ hψ hf hg
    (fun l=>hproj l.1 (F l)) (fun l=>hproj l.2 (G l))
  have hpow : bp (s:ℝ)≤bp (S:ℝ):=bp_le (by exact_mod_cast hsS)
  have hF : 0≤F₀:=mul_nonneg hB.le (bp_pos _).le
  have hscale : 0≤4*B*γ n*F₀:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB.le) hγn) hF
  have hbeta:=mul_le_mul_of_nonneg_left hpow hscale
  have hcost : 4*B*δ=ε/4 := by dsimp only [δ]; field_simp [hB.ne'] <;> ring
  have hrare : B^2*η=ε/4 := by dsimp only [η]; field_simp [hB.ne'] <;> ring
  change _≤_+ε
  change _≤_+4*B*δ+(2*γ n*F₀^2+4*B*γ n*bp (s:ℝ)*F₀)+B^2*η at hh
  rw [hcost,hrare] at hh
  nlinarith only [hh,hbeta,hsmall]

end
end Lax793645Proofs.Simplifications
