import Lax793645Proofs.Simplifications.QueryMomentExpansion
import Lax793645Proofs.Simplifications.UniformCornerBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  {p : Shape} {n N : ℕ}

/-- Finite raw high-moment inequality for the actual query. It keeps all
nominal columns and all original Gram equations. The three cutoffs control
nominal deficiency, additional image kernels, and cross-batch Gram rank. -/
theorem query_high_moment (v : Template p I) [DecidableEq (KeySlots p v.t)] (mixer : Mixer p n)
    (hN : 2*num (Full p n)<N) (q : I→F)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0 → ownPart v.t q (queryFromCoordinates v.t N x))
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (ψ : Wgt (Inputs p n I)) (hψ : ∀ x,|ψ x|≤1)
    (m : ℝ) (hm : 0≤m) (hslots : ∀ e,num (Port (cornerRoute v T) e)≤m)
    (hroom : 2*m-(N:ℝ)≤-1)
    (a d t : ℕ) (hrank : peakExpense T (Fin 3×KeySlots p v.t) 1≤(N:ℝ)/2) :
    |avg (pairW (raw mixer N) (raw mixer N)) (fun o=>(queryFourth v D ψ o)^Fintype.card T)|≤
      rawBatchBudget T (Fin 3×KeySlots p v.t) (Ports p) N
        (δ^2+bp (-(N:ℝ)/2)) m a d t+
      bp ((num (T×Fin 3)*num I-n)*a) := by
  classical
  let ρ:=pairW (raw mixer N) (raw mixer N)
  have hρ : IsLaw ρ:=pairW_law (raw_law mixer hN) (raw_law mixer hN)
  let E:=crowded (ownPort v.t)
  let Z:=directions (ownPort v.t) (ownMap v.t q)
  let ε:=δ^2+bp (-(N:ℝ)/2)
  have hε : 0≤ε:=add_nonneg (sq_nonneg _) (bp_pos _).le
  let K:=rawBatchBudget T (Fin 3×KeySlots p v.t) (Ports p) N ε m a d t
  have hK : 0≤K:=raw_batch_budget_nonneg ε m a hε d t
  let bad (y : T×Fin 3→Inputs p n I):=∃ e,
    (cornerNominal v y e).rank+a≤Fintype.card (Port (cornerRoute v T) e)
  let F (y : T×Fin 3→Inputs p n I) (o : UnitType p n N):=
    ∏ i:T,cornerProduct D
      (led i (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) (mergeR p o)))
  have hFb y o : |F y o|≤1 := by
    unfold F
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _)
      (fun _ _=>corner_product_bound D hD _)).trans_eq (by simp)
  have hlocal y : |avg ρ (F y)|≤K+ind (bad y) := by
    by_cases hy : bad y
    · rw [ind_one hy]
      exact (avg_bound1 hρ _ (hFb y)).trans (by linarith)
    rw [ind_zero hy,add_zero]
    have hdef e : num (Port (cornerRoute v T) e)-(cornerNominal v y e).rank≤(a:ℝ) := by
      have hh : Fintype.card (Port (cornerRoute v T) e)<(cornerNominal v y e).rank+a :=
        Nat.lt_of_not_ge (fun h=>hy ⟨e,h⟩)
      have hc : num (Port (cornerRoute v T) e)<((cornerNominal v y e).rank:ℝ)+a := by exact_mod_cast hh
      linarith
    have htrace : ∀ x,D x≠0 → traced (keyPlus x,keyMinus x) E Z := by
      intro x hx
      exact query_gram_trace v.t q x (hs x hx)
    have hh:=uniform_four_corner_bound (cornerRoute v T) mixer hN (cornerNominal v y)
      m a hm hslots hdef hroom E Z (corner_query_mask v) D δ hδ hD htrace hF d t hrank
    have he:=mapW_avg ρ (mergeR p) (fun x=>∏ i:T,cornerProduct D
      (led i (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) x)))
    dsimp only [ρ] at he
    rw [law_mergeR] at he
    rw [he] at hh
    exact hh
  rw [query_moment_expansion (T:=T)]
  refine (abs_avg_le unif_law.nz).trans ?_
  have hp y : |nominalCornerWeight ψ y*avg ρ (F y)|≤K+ind (bad y) := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right (nominal_corner_weight_bound ψ hψ y) (abs_nonneg _)).trans_eq
      (one_mul _)).trans (hlocal y)
  refine (avg_mono unif_law.nz hp).trans ?_
  rw [avg_add,unif_law.avg_const]
  exact add_le_add le_rfl (uniform_corner_nominal_tail (T:=T) v a)

end
end Lax793645Proofs.Simplifications
