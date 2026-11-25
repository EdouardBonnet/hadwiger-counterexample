import Lax793645Proofs.Simplifications.OneQueryFreeRows

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset Filter
open scoped Classical BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

/-- Counting linear maps into the kernel is sufficient. The number of
rows enters only a fixed prefactor, while the decay is exponential in n. -/
theorem one_tuple_rank_deficit (v : Template p I) [Nonempty (KeySlots p v.t)]
    {D : Type} [AddCommGroup D] [Module F D] [FiniteDimensional F D]
    (m : Mixer p n) (d : ℕ)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 2*d+3≤N)
    (T : D→ₗ[F]OneSlotKeys v.t N) (hT : Injective T) :
    pr (oneUnitRaw m N) (fun o=>Fintype.card (KeySlots p v.t)*d≤
      dim (((oneTupleFreeRows v o).comp T).ker))≤
      bp ((Fintype.card (KeySlots p v.t):ℝ)*d*dim D+(d:ℝ)^2+2-d*n) := by
  let k:=Fintype.card (KeySlots p v.t)*d
  letI : Fintype D:=Fintype.ofEquiv (Vec (Fin (dim D)))
    (Module.finBasis F D).equivFun.symm.toEquiv
  letI : Fintype (Vec (Fin k)→ₗ[F]D):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  let event (U : Vec (Fin k)→ₗ[F]D) (o : OneUnit p n N):=
    Injective U ∧ (oneTupleFreeRows v o).comp (T.comp U)=0
  have hsub (o : OneUnit p n N)
      (h : k≤dim (((oneTupleFreeRows v o).comp T).ker)) : ∃ U,event U o := by
    let A:=(oneTupleFreeRows v o).comp T
    have hd : finrank F (Vec (Fin k))≤finrank F A.ker:=by
      simpa only [dim_vec,Fintype.card_fin] using h
    obtain ⟨J,hJ⟩:=finrank_le_iff_exists_linearMap.mp hd
    refine ⟨A.ker.subtype.comp J,(Subtype.val_injective).comp hJ,?_⟩
    apply LinearMap.ext
    intro x
    exact (J x).property
  have hp (U : Vec (Fin k)→ₗ[F]D) :
      pr (oneUnitRaw m N) (event U)≤bp ((d:ℝ)^2+2-d*n) := by
    by_cases hU : Injective U
    · simpa only [event,hU,true_and] using
        one_tuple_rows_zero_cap v m d hroom hN (T.comp U) (hT.comp hU)
          (by simp only [dim_vec,Fintype.card_fin]; exact le_rfl)
    · simp only [event,hU,false_and,pr_false]
      exact (bp_pos _).le
  have hμ:=(one_unit_raw_law m hroom).nz
  refine ((pr_mono hμ hsub).trans (pr_exists_le hμ event)).trans ?_
  refine (Finset.sum_le_sum (fun U _=>hp U)).trans_eq ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space,←bp_add]
  congr 1
  simp only [dim,Module.finrank_linearMap,Module.finrank_pi_fintype,
    Module.finrank_self,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,
    Fintype.card_fin,k,Nat.cast_mul]
  ring

theorem one_tuple_deficit_calendar (v : Template p I) [Nonempty (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) (c : ℝ) :
    ∃ d : ℕ,1≤d ∧ ∀ R : ℕ,∀ᶠ n : ℕ in atTop,
      ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+1≤M*n →
      ∀ (π : Wgt (OneUnit p n (M*n))),
      (∀ o,π o≤bp (c*(M*n:ℕ))*oneUnitRaw m (M*n) o) →
      ∀ (D : Type) [AddCommGroup D] [Module F D] [FiniteDimensional F D],
      dim D≤R → ∀ T : D→ₗ[F]OneSlotKeys v.t (M*n),Injective T →
      pr π (fun o=>Fintype.card (KeySlots p v.t)*d≤
        dim (((oneTupleFreeRows v o).comp T).ker))≤bp (-10*n) := by
  obtain ⟨d,hd⟩:=exists_nat_gt (max (1:ℝ) (c*M+11))
  have hd1 : 1≤d:=by
    have hh: (1:ℝ)<d:=(le_max_left ..).trans_lt hd
    exact_mod_cast hh.le
  have hdc : c*M+11≤d:=((le_max_right ..).trans_lt hd).le
  refine ⟨d,hd1,fun R=>?_⟩
  let k:=Fintype.card (KeySlots p v.t)
  obtain ⟨L,hL⟩:=exists_nat_ge ((k:ℝ)*d*R+(d:ℝ)^2+2)
  filter_upwards [Filter.eventually_ge_atTop L,Filter.eventually_ge_atTop (2*d+3)]
    with n hn hn' m hroom π hcap D _ _ _ hD T hT
  have hnN : n≤M*n:=by simpa only [one_mul] using Nat.mul_le_mul_right n hM
  have hdim : (dim D:ℝ)≤R:=by exact_mod_cast hD
  have hnL : (L:ℝ)≤n:=by exact_mod_cast hn
  have hconst : (k:ℝ)*d*dim D+(d:ℝ)^2+2≤n:=by
    have hh:=mul_le_mul_of_nonneg_left hdim (by positivity : 0≤(k:ℝ)*d)
    linarith only [hh,hL,hnL]
  refine (pr_cap hcap _).trans ?_
  refine (mul_le_mul_of_nonneg_left
    (one_tuple_rank_deficit v m d hroom (hn'.trans hnN) T hT) (bp_pos _).le).trans ?_
  rw [←bp_add]
  apply bp_le
  have hh:=mul_le_mul_of_nonneg_right hdc (Nat.cast_nonneg n)
  push_cast
  dsimp only [k] at hconst
  nlinarith only [hh,hconst]

end
end Lax793645Proofs.Simplifications
