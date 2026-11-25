import Lax793645Proofs.Simplifications.SuccessfulCommonProjection
import Lax793645Proofs.Simplifications.LinearAdaptiveRebate
import Lax793645Proofs.Simplifications.ClippingContraction

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

/-- Common linear equations control clipped successful-query overlap.
The two acceptance filters are selected after the two independent leaves. -/
theorem clipped_successful_common_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c T ε : ℝ) (hT : 0<T) (hε : 0<ε) :
    ∃ S : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (UnitType p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*pairW (raw m (M*n)) (raw m (M*n)) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      let ν:=unifOn (queryReferenceSet (wA.pen t) z (M*n))
      let DA (l : Λ) (F : UnitType p n (M*n)→Prop):=
        density ν (mapW (wA.sales t z (π l) F m (a l)) (queryCoordinateEquiv t (M*n)).symm)
      let DB (l : Λ) (F : UnitType p n (M*n)→Prop):=
        density ν (mapW (wB.sales t z (π l) F m (a' l)) (queryCoordinateEquiv t (M*n)).symm)
      ∃ s : ℕ,s≤S ∧ ∃ C : Mat (Fin s) (Fin (M*n)×Bool×KeySlots p t),
        ∀ F G : Λ×Λ→UnitType p n (M*n)→Prop,
        avg (pairW μ μ) (fun l=>|rebate ν
          (fun x=>syrup T (DA l.1 (F l) x))
          (fun x=>syrup T (DB l.2 (G l) x)) C.mulVec|)≤ε := by
  obtain ⟨BA,hBA,hinitA⟩:=successful_query_linear_partition wA t z hA hp M hM c
  obtain ⟨BB,hBB,hinitB⟩:=successful_query_linear_partition wB t z hB hp M hM c
  let B:=T
  have hpos : 0<B:=hT
  let δ:=ε/(16*B)
  let η:=ε/(4*B^2)
  have hδ : 0<δ:=div_pos hε (mul_pos (by norm_num) hpos)
  have hη : 0<η:=div_pos hε (mul_pos (by norm_num) (sq_pos_of_pos hpos))
  obtain ⟨RA,hRA⟩:=hinitA δ hδ
  obtain ⟨RB,hRB⟩:=hinitB δ hδ
  let R:=RA+RB
  obtain ⟨S,hS⟩:=exists_nat_ge ((R:ℝ)*bp R/η)
  let F₀:=B*bp (R:ℝ)
  let γ (n:ℕ):=2*bp (num (crowded (ownPort t)))*bp (-((M*n:ℕ):ℝ)/2)
  obtain ⟨hγ,hνcal⟩:=query_reference_bias_calendar (wA.pen t) M hM
  change Tendsto γ atTop (nhds 0) at hγ
  have he : Tendsto (fun n=>γ n*(2*F₀^2+4*B*bp (S:ℝ)*F₀)) atTop (nhds 0):=by
    simpa only [zero_mul] using hγ.mul_const (2*F₀^2+4*B*bp (S:ℝ)*F₀)
  refine ⟨S,?_⟩
  filter_upwards [hRA,hRB,hνcal,
    he.eventually (eventually_le_nhds (half_pos hε))]
    with n hnA hnB hνn hsmall m hN Λ _ μ hμ π hπ hcap a a' ν DA DB
  obtain ⟨hν,hbias⟩:=hνn z
  have hγn : 0≤γ n:=mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le
  choose rA hrA PA hPA using fun l=>hnA m hN (π l) (hπ l) (hcap l) (a l)
  choose rB hrB PB hPB using fun l=>hnB m hN (π l) (hπ l) (hcap l) (a' l)
  let r (l:Λ):=rA l+rB l
  let P (l:Λ) : Mat (Fin (r l)) (Fin (M*n)×Bool×KeySlots p t):=Fin.append (PA l) (PB l)
  have hr l : r l≤R:=Nat.add_le_add (hrA l) (hrB l)
  obtain ⟨s,hs,C,hC⟩:=linear_adaptive_rebate μ hμ r P R hr η hη
  have hsS : s≤S:=by exact_mod_cast hs.trans hS
  refine ⟨s,hsS,C,fun F G=>?_⟩
  let rawA l:=DA l.1 (F l)
  let rawB l:=DB l.2 (G l)
  let f l x:=syrup T (rawA l x)
  let g l x:=syrup T (rawB l x)
  let φ (l:Λ×Λ) (x:Vec (Fin (r l.1))):=
    syrup T (cashbook ν (PA l.1).mulVec (rawA l) (((Fin.appendEquiv (rA l.1) (rB l.1)).symm x).1))
  let ψ (l:Λ×Λ) (x:Vec (Fin (r l.2))):=
    syrup T (cashbook ν (PB l.2).mulVec (rawB l) (((Fin.appendEquiv (rA l.2) (rB l.2)).symm x).2))
  have hφ l x : 0≤φ l x ∧ φ l x≤B:=syrup_range T _ hT.le
  have hψ l x : 0≤ψ l x ∧ ψ l x≤B:=syrup_range T _ hT.le
  have hf l : lcost ν (fun x=>φ l (P l.1*ᵥx)) (f l)≤δ:=by
    have hh x : φ l (P l.1*ᵥx)=syrup T (banner ν (PA l.1).mulVec (rawA l) x) := by
      dsimp only [φ,P]
      rw [append_mul_vec,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
    exact (clipping_lcost ν (banner ν (PA l.1).mulVec (rawA l)) (rawA l) hν.nz T).trans
      (by rw [lcost_symm]; exact (hPA l.1 (F l)).2)
  have hg l : lcost ν (fun x=>ψ l (P l.2*ᵥx)) (g l)≤δ:=by
    have hh x : ψ l (P l.2*ᵥx)=syrup T (banner ν (PB l.2).mulVec (rawB l) x) := by
      dsimp only [ψ,P]
      rw [append_mul_vec,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
    exact (clipping_lcost ν (banner ν (PB l.2).mulVec (rawB l)) (rawB l) hν.nz T).trans
      (by rw [lcost_symm]; exact (hPB l.2 (G l)).2)
  have hd l x : 0≤f l x ∧ f l x≤B:=syrup_range T _ hT.le
  have he' l x : 0≤g l x ∧ g l x≤B:=syrup_range T _ hT.le
  have hh:=hC ν hν (γ n) hγn hbias B δ hpos.le hδ.le f g φ ψ hd he' hφ hψ hf hg
  have hpow : bp (s:ℝ)≤bp (S:ℝ):=bp_le (by exact_mod_cast hsS)
  have hF : 0≤F₀:=mul_nonneg hpos.le (bp_pos _).le
  have hscale : 0≤4*B*γ n*F₀:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpos.le) hγn) hF
  have hbeta:=mul_le_mul_of_nonneg_left hpow hscale
  have hcost : 4*B*δ=ε/4 := by dsimp only [δ]; field_simp [hpos.ne']; ring
  have hrare : B^2*η=ε/4 := by dsimp only [η]; field_simp [hpos.ne']
  change _≤ε
  change _≤4*B*δ+(2*γ n*F₀^2+4*B*γ n*bp (s:ℝ)*F₀)+B^2*η at hh
  rw [hcost,hrare] at hh
  nlinarith only [hh,hbeta,hsmall]

end
end Lax793645Proofs.Simplifications
