import Lax793645Proofs.Simplifications.OneQueryCorrelation
import Lax793645Proofs.Simplifications.AuxiliaryNormalizedBatches

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {I T J : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [DecidableEq J] {p : Shape} {n N : ℕ}

variable {G : Type} [Fintype G] [DecidableEq G]

def auxiliaryRawBudget (I J G : Type) [Fintype I] [Fintype J] [Fintype G]
    (N : ℕ) (δ : ℝ) (a t : ℕ) : ℝ:=
  (4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*num G*a)*
    quadraticPatternBudget I (Bool×J) N (δ+bp (-(N:ℝ)/2)) t

theorem auxiliary_raw_budget_nonneg (δ : ℝ) (hδ : 0≤δ) (a t : ℕ) :
    0≤auxiliaryRawBudget I J G N δ a t :=
  mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (bp_pos _).le)
    (quadratic_pattern_budget_nonneg _ (add_nonneg hδ (bp_pos _).le) t)

/-- The actual frame law with nominal dependencies and exact image
kernels. Auxiliary dual vectors replace the entire kernel sieve. -/
theorem one_auxiliary_frame_bound (g : Route (I×J) G) (mixer : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3≤N) (A : NomQuery p n g)
    (hroom : ∀ i,2*((A i).rank:ℝ)+2≤N)
    (E : Rail J) (hE : ∀ u v,(u,v)∈E→(v,u)∈E)
    (hmask : ∀ v∈crowded g,(v.1.2,v.2.2)∈E)
    (f : I→Wgt (Rack J N)) (δ : ℝ) (hδ : 0≤δ)
    (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ B : Mat J J,Bᵀ=B→withinRail B E→∀ i ξ,
      |linearFourier (fun x=>phasedBy B (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤δ)
    (a t : ℕ) (hdef : ∀ i,num (Port g i)-(A i).rank≤(a:ℝ))
    (hrank : peakExpense I (Bool×J) 1≤(N:ℝ)/2) :
    |avg (oneForumLaw mixer N) (fun x=>∏ i,f i (led i (onePeek g A x)))|≤
      auxiliaryRawBudget I J G N δ a t := by
  obtain ⟨L,Q,hL,himage⟩:=one_raw_network_factored g mixer hN A
  have he:=mapW_avg (oneForumLaw mixer N) (onePeek g A) (fun x=>∏ i,f i (led i x))
  rw [himage] at he
  rw [←he]
  have hh:=auxiliary_normalized_batch_bound g E hE hmask L Q hL
    (fun i=>by simpa only [num,Fintype.card_fin] using hroom i)
    f δ hδ hb hf t hrank
  simp only [num,Fintype.card_fin] at hh
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (quadratic_pattern_budget_nonneg _
    (add_nonneg hδ (bp_pos _).le) t)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply bp_le
  have hs : (∑ i,(num (Port g i)-(A i).rank))≤num G*a:=by
    exact (Finset.sum_le_sum (fun i _=>hdef i)).trans_eq (by simp [num])
  dsimp only [num] at hs
  nlinarith only [mul_le_mul_of_nonneg_left hs (show 0≤2*(N:ℝ) by positivity)]

/-- Direct moments retain one independent nominal query per factor. -/
theorem one_auxiliary_query_moment (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (mixer : Mixer p n) (hN : Fintype.card (Row p n)+2*p.h+3≤N) (q : I→F)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1) (hs : ∀ x,D x≠0 → oneOwnPart v.t q x)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (ψ : Wgt (Inputs p n I)) (hψ : ∀ x,|ψ x|≤1)
    (m : ℝ) (hm : 0≤m) (hslots : ∀ e,num (Port (directQueryRoute v T) e)≤m)
    (hroom : 2*m+2≤N) (a t : ℕ)
    (hrank : peakExpense T (Bool×KeySlots p v.t) 1≤(N:ℝ)/2) :
    |avg (oneUnitRaw mixer N) (fun o=>(oneQueryCorrelation v D ψ o)^Fintype.card T)|≤
      auxiliaryRawBudget T (KeySlots p v.t) (Ports p) N δ a t+
        bp ((num T*num I-n)*a) := by
  classical
  let ρ:=oneUnitRaw mixer N
  have hρ : IsLaw ρ:=one_unit_raw_law mixer (by omega)
  let E:=crowded (ownPort v.t)
  let Z:=geoMatrix (ownPort v.t) (ownMap v.t q)
  let K:=auxiliaryRawBudget T (KeySlots p v.t) (Ports p) N δ a t
  have hK : 0≤K:=auxiliary_raw_budget_nonneg δ hδ a t
  let bad (y : T→Inputs p n I):=∃ e,
    (directQueryNominal v y e).rank+a≤Fintype.card (Port (directQueryRoute v T) e)
  let f (y : T→Inputs p n I) (o : OneUnit p n N):=
    ∏ i:T,D ((rackCoordinates (KeySlots p v.t) N).symm
      (led i (onePeek (directQueryRoute v T) (directQueryNominal v y) (oneMerge o))))
  have hb y o : |f y o|≤1:=by
    unfold f
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun _ _=>hD _)).trans_eq (by simp)
  have hlocal y : |avg ρ (f y)|≤K+ind (bad y):=by
    by_cases hy : bad y
    · rw [ind_one hy]
      exact (avg_bound1 hρ _ (hb y)).trans (by linarith)
    rw [ind_zero hy,add_zero]
    have hdef e : num (Port (directQueryRoute v T) e)-(directQueryNominal v y e).rank≤(a:ℝ):=by
      have hh : Fintype.card (Port (directQueryRoute v T) e)<(directQueryNominal v y e).rank+a:=
        Nat.lt_of_not_ge (fun h=>hy ⟨e,h⟩)
      have hh' : num (Port (directQueryRoute v T) e)<((directQueryNominal v y e).rank:ℝ)+a:=by exact_mod_cast hh
      linarith
    have hmask : ∀ z∈crowded (directQueryRoute v T),(z.1.2,z.2.2)∈E:=by
      intro z hz
      exact mem_filter.mpr ⟨mem_univ _,congrArg Prod.snd (mem_filter.mp hz).2⟩
    have hr e : 2*((directQueryNominal v y e).rank:ℝ)+2≤N:=by
      have hb' : ((directQueryNominal v y e).rank:ℝ)≤num (Port (directQueryRoute v T) e):=by
        exact_mod_cast Matrix.rank_le_card_width (directQueryNominal v y e)
      have hb : ((directQueryNominal v y e).rank:ℝ)≤m:=hb'.trans (hslots e)
      linarith
    have hh:=one_auxiliary_frame_bound (directQueryRoute v T) mixer hN (directQueryNominal v y)
      hr E (fun u v h=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2.symm⟩) hmask
      (fun _ x=>D ((rackCoordinates (KeySlots p v.t) N).symm x)) δ hδ
      (fun _ x=>hD _) (fun B hB hBE _ ξ=>by
        simpa only [LinearEquiv.symm_apply_apply] using
          quadratic_supported_fourier E Z D δ hs hF B hB hBE ξ) a t hdef hrank
    have he:=mapW_avg ρ oneMerge (fun x=>∏ i:T,D ((rackCoordinates (KeySlots p v.t) N).symm
      (led i (onePeek (directQueryRoute v T) (directQueryNominal v y) x))))
    dsimp only [ρ] at he
    rw [one_law_merge] at he
    rw [he] at hh
    exact hh
  rw [one_direct_moment_expansion]
  refine (abs_avg_le unif_law.nz).trans
    ((avg_mono unif_law.nz (g:=fun y=>K+ind (bad y)) (fun y=>?_)).trans ?_)
  · rw [abs_mul]
    have hp : |∏ t,ψ (y t)|≤1:=by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun _ _=>hψ _)).trans_eq (by simp)
    exact ((mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans_eq (one_mul _)).trans (hlocal y)
  · rw [avg_add,unif_law.avg_const]
    apply add_le_add le_rfl
    have hh:=query_nominal_kernel_tail (T:=T) (n:=n) v (globPort p v.t v.aim) (query_port_injective v)
      (fun _=>unif) (fun _=>unif_law) (fun _=>uniform_free_knobs) a
    simpa only [draws,←uniform_product_law,pr,bad,directQueryNominal] using hh

end
end Lax793645Proofs.Simplifications
