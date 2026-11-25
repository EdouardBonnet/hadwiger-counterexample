import Lax793645Proofs.Simplifications.OneSuccessfulCommonProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {q : Format} {d e : Rates} {b b' : Bool}

/-- The two sides may use different selectors, flavors, charts, status
prescriptions and binary scripts. Only their reference key variety is shared. -/
theorem one_asymmetric_successful_common_projection (wA : Quill p q d b) (wB : Quill p q e b')
    (t : Tagging p (Messenger q)) [DecidableEq (KeySlots p t)]
    (z : Messenger q→F) (hA : wA.moral t z) (hB : wB.moral t z) (hp : 1≤p.r)
    (M : ℕ) (hM : 1≤M) (c ε : ℝ) (hε : 0<ε) :
    ∃ S : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤M*n →
      ∀ (Λ : Type) [Fintype Λ] (μ : Wgt Λ),IsLaw μ →
      ∀ (π : Λ→Wgt (OneUnit p n (M*n))),(∀ l,IsLaw (π l)) →
      (∀ l o,π l o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (a : Λ→Charts p n d) (a' : Λ→Charts p n e),
      let ν:=unifOn (oneQueryReferenceSet (wA.pen t) z (M*n))
      let DA (l : Λ) (F : OneUnit p n (M*n)→Prop):=
        density ν (oneSales wA t z (π l) F m (a l))
      let DB (l : Λ) (F : OneUnit p n (M*n)→Prop):=
        density ν (oneSales wB t z (π l) F m (a' l))
      ∃ s : ℕ,s≤S ∧ ∃ C : Mat (Fin s) (Fin (M*n)×Bool×KeySlots p t),
        ∀ F G : Λ×Λ→OneUnit p n (M*n)→Prop,
        avg (pairW μ μ) (fun l=>dip ν (banner ν C.mulVec (DA l.1 (F l)))
          (banner ν C.mulVec (DB l.2 (G l))))≤
        avg (pairW μ μ) (fun l=>dip ν (DA l.1 (F l)) (DB l.2 (G l)))+ε := by
  obtain ⟨BA,hBA,hinitA⟩:=one_successful_query_linear_partition wA t z hA hp M hM c
  obtain ⟨BB,hBB,hinitB⟩:=one_successful_query_linear_partition wB t z hB hp M hM c
  obtain ⟨CA,hCA,hboundA⟩:=one_successful_linear_density_bound wA t z hA hp M hM c
  obtain ⟨CB,hCB,hboundB⟩:=one_successful_linear_density_bound wB t z hB hp M hM c
  let B:=max (max BA BB) (max CA CB)
  have hBA' : BA≤B:=(le_max_left ..).trans (le_max_left ..)
  have hBB' : BB≤B:=(le_max_right ..).trans (le_max_left ..)
  have hCA' : CA≤B:=(le_max_left ..).trans (le_max_right ..)
  have hCB' : CB≤B:=(le_max_right ..).trans (le_max_right ..)
  have hpos : 0<B:=lt_of_lt_of_le zero_lt_one (hBA.trans hBA')
  let δ:=ε/(16*B)
  let η:=ε/(4*B^2)
  have hδ : 0<δ:=div_pos hε (mul_pos (by norm_num) hpos)
  have hη : 0<η:=div_pos hε (mul_pos (by norm_num) (sq_pos_of_pos hpos))
  obtain ⟨RA,hRA⟩:=hinitA δ hδ
  obtain ⟨RB,hRB⟩:=hinitB δ hδ
  let R:=RA+RB
  obtain ⟨S,hS⟩:=exists_nat_ge ((R:ℝ)*bp R/η)
  let F₀:=B*bp (R:ℝ)
  let γ (n:ℕ):=2*bp (quadraticReferenceCost (crowded (ownPort t)))*bp (-((M*n:ℕ):ℝ)/2)
  obtain ⟨hγ,hνcal⟩:=one_query_reference_bias_calendar (wA.pen t) M hM
  change Tendsto γ atTop (nhds 0) at hγ
  have he : Tendsto (fun n=>γ n*(2*F₀^2+4*B*bp (S:ℝ)*F₀)) atTop (nhds 0):=by
    simpa only [zero_mul] using hγ.mul_const (2*F₀^2+4*B*bp (S:ℝ)*F₀)
  refine ⟨S,?_⟩
  filter_upwards [hRA,hRB,hboundA S,hboundB S,hνcal,
    he.eventually (eventually_le_nhds (half_pos hε))]
    with n hnA hnB hbA hbB hνn hsmall m hN Λ _ μ hμ π hπ hcap a a' ν DA DB
  obtain ⟨hν,hbias⟩:=hνn z
  have hγn : 0≤γ n:=mul_nonneg (mul_nonneg (by norm_num) (bp_pos _).le) (bp_pos _).le
  choose rA hrA PA hPA using fun l=>hnA m hN (π l) (hπ l) (hcap l) (a l)
  choose rB hrB PB hPB using fun l=>hnB m hN (π l) (hπ l) (hcap l) (a' l)
  let r (l:Λ):=rA l+rB l
  let P (l:Λ) : Mat (Fin (r l)) (Fin (M*n)×Bool×KeySlots p t):=Fin.append (PA l) (PB l)
  have hr l : r l≤R:=Nat.add_le_add (hrA l) (hrB l)
  obtain ⟨s,hs,C,hC⟩:=linear_adaptive_overlap μ hμ r P R hr η hη
  have hsS : s≤S:=by exact_mod_cast hs.trans hS
  refine ⟨s,hsS,C,fun F G=>?_⟩
  let f l:=DA l.1 (F l)
  let g l:=DB l.2 (G l)
  let φ (l:Λ×Λ) (x:Vec (Fin (r l.1))):=
    cashbook ν (PA l.1).mulVec (f l) (((Fin.appendEquiv (rA l.1) (rB l.1)).symm x).1)
  let ψ (l:Λ×Λ) (x:Vec (Fin (r l.2))):=
    cashbook ν (PB l.2).mulVec (g l) (((Fin.appendEquiv (rA l.2) (rB l.2)).symm x).2)
  have hφ l x : 0≤φ l x ∧ φ l x≤B := by
    have hh:=cashbook_bound_of_banner ν (f l) hν.nz (PA l.1).mulVec BA
      (zero_le_one.trans hBA) ((hPA l.1 (F l)).1)
      (((Fin.appendEquiv (rA l.1) (rB l.1)).symm x).1)
    exact ⟨hh.1,hh.2.trans hBA'⟩
  have hψ l x : 0≤ψ l x ∧ ψ l x≤B := by
    have hh:=cashbook_bound_of_banner ν (g l) hν.nz (PB l.2).mulVec BB
      (zero_le_one.trans hBB) ((hPB l.2 (G l)).1)
      (((Fin.appendEquiv (rA l.2) (rB l.2)).symm x).2)
    exact ⟨hh.1,hh.2.trans hBB'⟩
  have hf l : lcost ν (fun x=>φ l (P l.1*ᵥx)) (f l)≤δ:=by
    have hh x : φ l (P l.1*ᵥx)=banner ν (PA l.1).mulVec (f l) x := by
      dsimp only [φ,P]
      rw [append_mul_vec,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
    rw [lcost_symm]
    exact (hPA l.1 (F l)).2
  have hg l : lcost ν (fun x=>ψ l (P l.2*ᵥx)) (g l)≤δ:=by
    have hh x : ψ l (P l.2*ᵥx)=banner ν (PB l.2).mulVec (g l) x := by
      dsimp only [ψ,P]
      rw [append_mul_vec,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
    rw [lcost_symm]
    exact (hPB l.2 (G l)).2
  have hd l H x : 0≤DA l H x:=div_nonneg
    (one_sales_nonneg wA t z (π l) H m (a l) (hπ l).nz x) (hν.nz x)
  have he' l H x : 0≤DB l H x:=div_nonneg
    (one_sales_nonneg wB t z (π l) H m (a' l) (hπ l).nz x) (hν.nz x)
  have hpd l H x : 0≤banner ν C.mulVec (DA l H) x ∧ banner ν C.mulVec (DA l H) x≤B := by
    have hh:=hbA m hN (π l) (hπ l) (hcap l) (a l) s hsS C H x
    exact ⟨hh.1,hh.2.trans hCA'⟩
  have hpe l H x : 0≤banner ν C.mulVec (DB l H) x ∧ banner ν C.mulVec (DB l H) x≤B := by
    have hh:=hbB m hN (π l) (hπ l) (hcap l) (a' l) s hsS C H x
    exact ⟨hh.1,hh.2.trans hCB'⟩
  have hh:=hC ν hν (γ n) hγn hbias B δ hpos.le hδ.le f g φ ψ
    (fun l=>hd l.1 (F l)) (fun l=>he' l.2 (G l)) hφ hψ hf hg
    (fun l=>hpd l.1 (F l)) (fun l=>hpe l.2 (G l))
  have hpow : bp (s:ℝ)≤bp (S:ℝ):=bp_le (by exact_mod_cast hsS)
  have hF : 0≤F₀:=mul_nonneg hpos.le (bp_pos _).le
  have hscale : 0≤4*B*γ n*F₀:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpos.le) hγn) hF
  have hbeta:=mul_le_mul_of_nonneg_left hpow hscale
  have hcost : 4*B*δ=ε/4 := by dsimp only [δ]; field_simp [hpos.ne']; ring
  have hrare : B^2*η=ε/4 := by dsimp only [η]; field_simp [hpos.ne']
  change _≤_+ε
  change _≤_+4*B*δ+(2*γ n*F₀^2+4*B*γ n*bp (s:ℝ)*F₀)+B^2*η at hh
  rw [hcost,hrare] at hh
  nlinarith only [hh,hbeta,hsmall]

end
end Lax793645Proofs.Simplifications
