/- Adapts the adaptive finite-list estimate from the vendored Apache-2.0
OpenAI AdaptiveRecordBounds module to the one-frame raw law. -/
import Lax793645Proofs.Simplifications.OneIndependentTestWitnesses

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}

def oneQuest (p : Shape) (r k n N : ℕ) (H ε : ℝ) :=
  ∀ x : ℕ,x≤r →
    bp ((x:ℝ)*(2*N))*bp (0.51*k*(2*N))*(H*oneHeatRate p n N ε x k)≤bp (-0.2*(2*N))

namespace OneBazaar
variable (s : OneBazaar p n r T)

set_option maxHeartbeats 800000 in
private theorem probe_event {w : Wgt (OneUnit p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1) {k : ℕ}
    {q : Comp p.g→ℕ} (R : ImageTuple (Comp p.g) q (2*N)) (F : Catalog p T r q)
    (hq : symTotal p q=k) (hr : ∀ M Z,(↑(F M Z).card:ℝ) ≤ bp (0.51*k*(2*N)))
    (m : Mixer p n) {ε H : ℝ} (he₀ : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ε (imagePlanRank a.sp)) (hH : 0≤H) (hZ : oneQuest p r k n N H ε)
    (hg : ∀ x,w x≤H*oneUnitRaw m N x)
    (hT : num (SymAtlas p r T) ≤ bp (0.002*(2*N))) :
    pr w (fun x => s.atList S j R F x ∧ oneTupleGlimpse x j R) ≤ bp (-0.1*(2*N)) := by
  classical
  let P (M : SymAtlas p r T) (z : SymBatch M (2*N)) (v : ImageTuple (Comp p.g) q (2*N)) :=
    fun x => oneBasisFrom (x : OneUnit p n N) j z ∧ oneTupleGlimpse x j R ∧ oneThermal x S R=v
  let L (M : SymAtlas p r T) (x) := symStandard M ∧ ∃ z,∃ v∈ F M z,P M z v x
  have he x : w x≠0 → s.atList S j R F x ∧ oneTupleGlimpse x j R →
      ∃ M,L M x := by
    rintro hx ⟨hx',hy⟩
    exact ⟨s.ix x,(h x hx).1,s.bag (s.ix x) j x, oneThermal x S R,hx',
      ((h x hx).2 j).1,hy,rfl⟩
  have ht (M : SymAtlas p r T) : pr w (L M) ≤ bp (-0.2*(2*N)) := by
    by_cases hu : symStandard M
    · let x := symCells M
      have hb (z : SymBatch M (2*N)) :
          pr w (fun y => ∃ v∈F M z,P M z v y) ≤ bp (0.51*k*(2*N))*(H*oneHeatRate p n N ε x k) := by
        have ha v : pr w (P M z v) ≤ H*oneHeatRate p n N ε x k := by
          rw [← hq]; exact (pr_cap hg _).trans
            (mul_le_mul_of_nonneg_left (one_heat_rate _ S hi R v z m he₀) hH)
        refine (pr_union_le hw.nz (F M z) (P M z)).trans ((Finset.sum_le_sum fun v _ => ha v).trans ?_)
        rw [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (hr M z)
        unfold oneHeatRate
        exact mul_nonneg hH (mul_nonneg (bp_pos _).le (bp_pos _).le)
      simp only [L,hu,true_and]
      refine (pr_exists_le hw.nz (fun z y => ∃ v∈F M z,P M z v y)).trans
        ((Finset.sum_le_sum (fun z _ => hb z)).trans ?_)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_space]
      rw [show dim (SymBatch M (2*N))=(2*N)*x from image_tuple_dimension _ _,
        Nat.cast_mul]
      push_cast
      rw [show (2*(N:ℝ))*(x:ℝ)=(x:ℝ)*(2*N) by ring,←mul_assoc]
      exact hZ x hu.2.1
    simp only [L,hu,false_and,pr_false]
    exact (bp_pos _).le
  refine ((pr_on_mono hw.nz he).trans (pr_exists_le hw.nz L)).trans
    ((Finset.sum_le_sum fun i _ => ht i).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul]
  apply (mul_le_mul_of_nonneg_right hT (bp_pos _).le).trans
  rw [←bp_add]
  apply bp_le; linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]

set_option maxHeartbeats 600000 in
theorem frequent_sparse {w : Wgt (OneUnit p n N)} {Δ}
    (hw : IsLaw w) (h : s.opened Δ w)
    (S : Party) (j : Bool) (hi : S j=1)
    (k d : ℕ) (hh : k ≤ d) (l : ℝ) (hl : 0< l)
    (hC : ∀ C : SymCover p (2*N),oneCoverDimension C≤d → pr w (fun x => symOffsetCover (s.ix x) ≤ C) ≤ l)
    (hb : ∀ A M Z,(↑(s.bids w S j A M Z).card:ℝ) ≤ bp (0.51*(2*N)))
    (m : Mixer p n) {ε H L : ℝ} (hN : Fintype.card (Row p n)+2*p.h+1≤N)
    (he : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ε (imagePlanRank a.sp))
    (hH : 0≤H) (hZ : oneQuest p r k n N H ε)
    (hg : ∀ x,w x≤H*oneUnitRaw m N x)
    (hL : 0 ≤ L) (hv : ∀ i o,mapW w (fun x=>x i) o≤L*oneRaw m N o)
    (hT : num (SymAtlas p r T) ≤ bp (0.002*(2*N)))
    (hk : oneGlimpseBill p k L+bp (-0.1*(2*N))<l^(k+1)) :
    pr (pairW w w) (fun x => s.frequent w S j (s.ix x.1) (s.ix x.2) x.2) ≤5*l := by
  classical
  by_contra! hr
  obtain ⟨q,R,F,hq,hR,hF,hx⟩ := s.shooting hw S j k d hh l hl hr.le hC hb
  have hp := s.probe_event hw h S j hi R F hq hF m he hH hZ hg hT
  have hq' z : q z≤ k := hq ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (q i))
    (Finset.mem_univ z)
  have hu := one_tuple_glimpse_failure R hR hq' hw.sub m j hL (hv j) hN
  let T := fun (x : OneUnit p n N) => oneTupleGlimpse x j R
  let V := s.atList S j R F
  have hh' x : V x → ¬T x ∨ (V x ∧ T x) := fun h => by by_cases ht:T x <;> simp [ht,h]
  exact not_lt_of_ge
    (hx.trans ((pr_mono hw.nz hh').trans ((pr_or_le hw.nz).trans (add_le_add hu hp)))) hk

end OneBazaar
end
end Lax793645Proofs.Simplifications
