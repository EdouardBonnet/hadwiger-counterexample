import Lax793645Proofs.Simplifications.OneUnaryConcentration
import Lax793645Proofs.Simplifications.OneCommonPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionExactification

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneTabErr (p : Shape) (l : Tag p.g) (s : Label p.b) (o : OneOrient p n N)
    (x : F) (g : OneAugur p N) (f : F) :=
  let v := Template.solo p l s Flavor.full
  let u:= scopedBit p n l Flavor.full x
  pr u (fun i=> g l x (oneDesc v i o)≠ f*x)
def oneTabRef (p : Shape) (l : Tag p.g) (x : F) (g : OneAugur p N) (f : F) :=
  pr (oneLawOmega p N l x) (fun i=> g l x i≠f*x)

theorem one_tab_calendar (p : Shape) (M : ℕ) (hM : 1≤M) (hg : 3≤ p.g) (hr : 1≤p.r) (hj : 1≤p.j)
    (l : Tag p.g) (s : Label p.b) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (m : Mixer p n), Fintype.card (Row p n)+2*p.h+3≤N →
    ∀ (g : OneAugur p N) (x f : F),
      oneTabRef p l x g f ≤1/100 →
      pr (oneRaw m N) (fun i => 1/32<oneTabErr p l s i x g f)≤ bp (-(1/8:ℝ)*n) := by
  classical
  let v := Template.solo p l s Flavor.full
  filter_upwards [one_flat_recital v M hM hj (1/100) (by norm_num),eventually_ge_atTop (2*p.r)]
    with n hn hq N m hN g x f he
  let w := scopedBit p n l Flavor.full x
  obtain ⟨d,hd,hg,_⟩ := generic_summary p hg l x 0
  have hw := dial_law p n l Flavor.full x hr hq ⟨d,hd,hg⟩
  have hy := normW_carried (subW_carried (spins p n) (fun i=>dialed p l Flavor.full i=x))
  let T (i : OneAtomKey (p:=p) l N) := ind (g l x i≠ f*x)
  have ht (i) : |T i|≤1 := by unfold T; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _
  have hh := hn m w x hw hy (scopedZ_bit p n _ _ _ hw) hN T ht
  refine (pr_mono (one_raw_law m (by omega)).nz (fun i hi => ?_)).trans hh
  change 1/100≤ |oneTabErr p l s i x g f-oneTabRef p l x g f|
  exact le_trans (by linarith only [he,hi]) (le_abs_self _)

def oneWhisper (p : Shape) (g : OneAugur p N) (x : F) (i : OneOrient p n N) :=
  ∀ l s b,oneTabErr p l s i b g x ≤1/32

theorem one_hush_calendar (p : Shape) (M : ℕ) (hM : 1≤M) (hg : 3≤p.g)
    (hr : 1≤p.r) (hj : 1≤p.j) :
    ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (m : Mixer p n),Fintype.card (Row p n)+2*p.h+3≤N →
    ∀ (g : OneAugur p N) (x : F), (∀ i b,oneTabRef p i b g x≤1/100) →
    pr (oneRaw m N) (fun i=>¬ oneWhisper p g x i)≤bp (-(1/16:ℝ)*n) := by
  classical
  let A:= Tag p.g × Label p.b × F
  filter_upwards [eventually_all.mpr (fun i:A => one_tab_calendar p M hM hg hr hj i.1 i.2.1),
    pay_nat (a:=1/8) (b:=1/16) (num A) (by norm_num)]
    with n hn hd N m hN g f hw
  let T (i:A) (o:OneOrient p n N) := 1/32<oneTabErr p i.1 i.2.1 o i.2.2 g f
  have he o (h : ¬oneWhisper p g f o) : ∃ i,T i o := by
    unfold oneWhisper at h
    push Not at h
    obtain ⟨l,s,b,h⟩:=h; exact ⟨(l,s,b),h⟩
  have hm := one_raw_law (N:=N) m (by omega)
  have ht (i:A) : pr (oneRaw m N) (T i)≤bp (-(1/8:ℝ)*n) := hn i m hN g _ f (hw _ _)
  exact ((pr_mono hm.nz he).trans (pr_exists_le hm.nz T)).trans
    (((Finset.sum_le_sum (fun i _=>ht i)).trans_eq (by simp [num])).trans hd)

set_option maxHeartbeats 800000 in
theorem one_hush_vat (w : Pdual p n) (E : Finset (Label p.b)) (i : OneOrient p n N) (g : OneAugur p N) (f : F)
    (hE : (E.card:ℝ)< bp ((p.b:ℝ)-2*p.j)) (h : onePostulates i g w E (1/16))
    (hz : oneWhisper p g f i) (hg : Odd p.g) (hr : 1≤p.r) (hn : 2*p.r≤n) :
    f=0∧silent w := by
  classical
  refine exact_vat w E f hE hg hn hr (fun l s hs=>?_)
  let v := Template.solo p l s Flavor.full; let μ:= spins p n
  let q (x: Knobs p.g n) := dialed p l Flavor.full x
  let Q (b:F) (x) := q x=b
  let S (b:F) x := g l b (oneDesc v x i) ≠ f*b
  let P x:= S (q x) x
  have hμ:= spins_law p n
  have hp :
      pr μ P ≤ 2*(1/32) := by
    have ht b : pr μ (fun x=>Q b x∧S b x) ≤ 1/32 := by
      rw [pr_of_on hμ.nz]
      have hh : pr (onW μ (Q b)) (S b) ≤1/32 := hz _ _ _
      exact (mul_le_mul ((pr_le_tot hμ.nz).trans hμ.total.le) hh
        (pr_nonneg (normW_subLaw (subW_nonneg hμ.nz _)).nz) zero_le_one).trans_eq (one_mul _)
    calc _
      _ ≤ ∑ b:F,pr μ (fun i=>Q b i ∧ S b i) :=
            (pr_mono hμ.nz (fun i h=>show ∃ b,Q b i∧S b i from ⟨q i,rfl,h⟩)).trans
            (pr_exists_le hμ.nz _)
      _ ≤ _ := (Finset.sum_le_sum fun i _=>ht i).trans_eq (by simp [F,ZMod.card])
  let T x:= oneMismatch g w l s Flavor.full i x
  have ht : pr μ T≤ 1/16 := h _ hs _ _
  have he x (h : w (useAtom p l s Flavor.full x)≠ f*q x) : T x∨P x := by
    by_contra! hh
    exact h ((not_ne_iff.mp hh.1).trans (not_ne_iff.mp hh.2))
  exact lt_of_le_of_lt ((pr_mono hμ.nz he).trans (pr_or_le hμ.nz)) (by linarith only [ht,hp])
end
end Lax793645Proofs.Simplifications
