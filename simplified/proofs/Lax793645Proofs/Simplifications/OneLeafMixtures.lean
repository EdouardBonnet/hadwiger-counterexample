import Lax793645Proofs.Simplifications.ImageLeafMixtures
import Lax793645Proofs.Simplifications.OneClosedImagePartitions
import Lax793645Proofs.Simplifications.OneSparseUsual

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

abbrev OneLeafMixture (p : Shape) (n N : ℕ):=
  ImageLeafMixture (OneUnit p n N) (Comp p.g) (OneColumn p n) (2*N)

def oneLeafStrength (s : OneLeafMixture p n N) (w : Wgt (OneUnit p n N))
    (m : Mixer p n) (D ζ : ℝ) (K : ℕ):=
  s.strength oneCoordinateImages (onePinClosure p n) w (oneUnitRaw m N) D ζ K

theorem one_first_leaves (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (D ζ : ℝ) (K : ℕ) (hz : 0<ζ) (hz' : ζ<1)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hroom : (dim (OneFull p n):ℝ)+2≤((ζ/6)/4)*(2*N))
    (hcap : ∀ x,w x≤bp (D*(2*N))*oneUnitRaw m N x) (hw : ∀ x,0≤w x)
    (P : OneUnit p n N→Prop) (hK : D+ζ≤((ζ/6)-(ζ/6)/4)*K) :
    ∃ s : OneLeafMixture p n N,oneLeafStrength s w m (D+K+1) ζ K ∧ s.within P ∧
      pr w P-bp (-ζ*(2*N))≤s.amount w := by
  have hn : 0<2*N:=by omega
  simpa only [oneLeafStrength,Nat.cast_mul,Nat.cast_ofNat] using
    ImageLeafMixture.first oneCoordinateImages (by decide : 1≤6) (onePinClosure p n)
      one_pin_closure_bot ζ D K hz hz' hn
      (fun a ha=>one_closed_pin_cap m a ha (by linarith) hN hroom)
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcap) hw P hK

/-- Parameter order for closed-pin preparation: all construction and
spreading constants are fixed before the ambient multiplier. -/
theorem one_leaf_calendar (p : Shape) {ζ : ℝ} (hz : 0<ζ) (hz' : ζ<1) (D : ℝ) (K : ℕ)
    (hK : D+ζ≤((ζ/6)-(ζ/6)/4)*K) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m : Mixer p n) (w : Wgt (OneUnit p n N)),
        (∀ x,w x≤bp (D*(2*N))*oneUnitRaw m N x) →(∀ x,0≤w x) →
        ∀ P : OneUnit p n N→Prop,
        ∃ s : OneLeafMixture p n N,oneLeafStrength s w m (D+K+1) ζ K ∧ s.within P ∧
          pr w P-bp (-ζ*(2*N))≤s.amount w := by
  filter_upwards [columns_budget p (δ:=1) zero_lt_one 4 5 (by norm_num) (by norm_num),
    columns_budget p (δ:=ζ/12) (by positivity) 4 5 (by norm_num) (by norm_num)]
    with M hA hB
  filter_upwards [eventually_ge_atTop 1] with n hn N m w hc hw P
  have hA:=hA n hn
  have hB:=hB n hn
  rw [one_mul] at hA
  have hf : num (Full p n)=num (Row p n)+p.h:=by simp [num,Full]
  rw [hf] at hA hB
  have hrow : 0≤num (Row p n):=by unfold num; positivity
  have hh : 0≤(p.h:ℝ):=Nat.cast_nonneg _
  have hN : 2*dim (OneFull p n)+3≤N := by
    rw [one_full_dimension]
    have hb : 2*(num (Row p n)+2*p.h)+3≤N:=by linarith only [hA,hrow]
    exact_mod_cast hb
  have hroom : (dim (OneFull p n):ℝ)+2≤((ζ/6)/4)*(2*N) := by
    rw [one_full_dimension]
    push_cast
    change num (Row p n)+2*p.h+2≤_
    linarith only [hB,hrow,hh]
  exact one_first_leaves m w D ζ K hz hz' hN hroom hc hw P hK

/-- The initial rank cutoff and closed-pin partition are obtained in one
law, with both errors charged before normalization of the retained union. -/
theorem one_initial_leaf_calendar (p : Shape) (D : ℕ) (hD : 0<D)
    {ζ : ℝ} (hz : 0<ζ) (hz' : ζ<1) (K : ℕ)
    (hK : (D:ℝ)+ζ≤((ζ/6)-(ζ/6)/4)*K) :
    ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,let N:=M*n;
      ∀ (m : Mixer p n) (w : Wgt (OneUnit p n N)),IsLaw w →
        (∀ x,w x≤bp ((D:ℝ)*(2*N))*oneUnitRaw m N x) →
        ∀ P : OneUnit p n N→Prop,carried w P →
        ∃ s : OneLeafMixture p n N,oneLeafStrength s w m (D+K+1) ζ K ∧
          s.within (fun x=>P x ∧ oneJoins x≤2*D) ∧
          1-bp (-(D:ℝ)/2*(2*N))-bp (-ζ*(2*N))≤s.amount w := by
  filter_upwards [one_leaf_calendar p hz hz' (D:ℝ) K hK,one_sparse_usual p D hD]
    with M hL hS
  filter_upwards [hL,hS] with n hL hS N m w hw hc P hP
  obtain ⟨s,hs,hwithin,hmass⟩:=hL m w hc hw.nz (fun x=>P x ∧ oneJoins x≤2*D)
  refine ⟨s,hs,hwithin,?_⟩
  have herr:=hS m w hc
  have hret:=pr_shield hw.nz P (fun x=>oneJoins x≤2*D)
  rw [(carried_iff_pr hw.nz).mp hP,hw.total] at hret
  simp only [not_le] at hret
  linarith only [herr,hret,hmass]

end
end Lax793645Proofs.Simplifications
