import Lax793645Proofs.Simplifications.MomentBudgetScales
import Lax793645Proofs.Simplifications.QueryCappedMoment

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The Fourier cutoff is chosen after the desired exponential rate;
the repetition fraction and construction constants remain fixed. -/
theorem query_moment_decay {I : Type} [Fintype I] [DecidableEq I]
    {p : Shape} (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (M : ℕ) (hM : 1≤M) :
    ∃ s : ℕ,0<s ∧ ∀ H : ℝ,0≤H → ∃ δ : ℝ,0<δ ∧
      ∀ᶠ n : ℕ in atTop, 0<n/s ∧
      ∀ (mixer : Mixer p n),2*num (Full p n)<(M*n:ℕ) →
      ∀ (q : I→F) (D : Wgt (KeyCoordinates (KeySlots p v.t) (M*n)))
        (ψ : Wgt (Inputs p n I)),
      (∀ x,|D x|≤1) → (∀ x,D x≠0 → ownPart v.t q (queryFromCoordinates v.t (M*n) x)) →
      (∀ ξ,|linearFourier D ξ|≤δ) → (∀ x,|ψ x|≤1) →
      avg (pairW (raw mixer (M*n)) (raw mixer (M*n)))
        (fun o=>(queryFourth v D ψ o)^(n/s))≤bp (-H*n) := by
  let J:=Fin 3×KeySlots p v.t
  let k:=num J
  have hk : 0≤k:=Nat.cast_nonneg _
  obtain ⟨s,hs,hcal⟩:=raw_budget_calendar J (Ports p) M hM (num I) k (Nat.cast_nonneg _) hk
  refine ⟨s,hs,fun H hH=>?_⟩
  obtain ⟨a,d,t,u,hu,hcal⟩:=hcal H hH
  let δ:=bp (-(u+1)/2)
  have hδ : 0<δ:=bp_pos _
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcal,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (2*(u+1)))] with n hn hnu
  obtain ⟨hl,hr,ht,hbudget⟩:=hn
  refine ⟨hl,fun mixer hN q D ψ hD hsup hF hψ=>?_⟩
  have hNM : (n:ℝ)≤(M*n:ℕ):=by
    have hMr : (1:ℝ)≤M:=by exact_mod_cast hM
    simpa only [Nat.cast_mul,one_mul] using mul_le_mul_of_nonneg_right hMr (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hε : δ^2+bp (-(M*n:ℕ)/2)≤bp (-u):=by
    have hsq : δ^2=bp (-(u+1)):=by
      dsimp only [δ]
      rw [pow_two,←bp_add]
      congr 1
      ring
    rw [hsq]
    have hh : bp (-(M*n:ℕ)/2)≤bp (-(u+1)):=bp_le (by linarith only [hnu,hNM])
    calc
      _≤bp (-(u+1))+bp (-(u+1)):=add_le_add le_rfl hh
      _=bp (-u):=by
        rw [show -u=1+(-(u+1)) by ring,bp_add,bp_one]
        ring
  have hslots e : num (Port (cornerRoute v (Fin (n/s))) e)≤k*(n/s:ℕ):=by
    have hh:=port_limit (cornerRoute v (Fin (n/s))) e
    simpa only [cornerRoute,num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,k,J,mul_comm] using hh
  have hraw:=query_high_moment (T:=Fin (n/s)) v mixer hN q D δ hδ.le hD hsup hF ψ hψ
    (k*(n/s:ℕ)) (mul_nonneg hk (Nat.cast_nonneg _)) hslots hr a d t ht
  have hm:=raw_budget_mono (I:=Fin (n/s)) (J:=J) (G:=Ports p) (N:=M*n)
    (δ^2+bp (-(M*n:ℕ)/2)) (bp (-u)) (k*(n/s:ℕ)) a
    (add_nonneg (sq_nonneg _) (bp_pos _).le) hε d t
  have hnumeq : bp ((num (Fin (n/s)×Fin 3)*num I-n)*a)=
      bp ((3*(n/s:ℕ)*num I-n)*a):=by
    congr 1
    simp only [num,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    ring
  simp only [Fintype.card_fin,hnumeq] at hraw
  exact (le_abs_self _).trans (hraw.trans ((add_le_add hm le_rfl).trans hbudget))

end
end Lax793645Proofs.Simplifications
