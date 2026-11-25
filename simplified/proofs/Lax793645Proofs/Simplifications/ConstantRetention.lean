import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PartitionDeletionBounds
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Finite retention, without any rate or filter assumptions. -/
theorem fixed_mass_trim {A : Type} [Fintype A] (w : Wgt A)
    (hw : ∀ x,0≤w x) (T V P : A→Prop) (a b δ : ℝ)
    (ha : 0<a) (hb : 0<b) (hδ : 0≤δ) (hsmall : δ≤a*b/2)
    (hT : a≤pr w T) (hP : b≤pr (onW w T) P)
    (hsub : ∀ x,V x→T x∧P x)
    (hloss : pr w (fun x=>T x∧P x∧¬V x)≤δ) :
    a*b/2≤pr w V ∧ ∀ Q : A×A→Prop,
      pr (pairW (onW (onW w T) P) (onW (onW w T) P)) Q-2*δ/(a*b)≤
        pr (pairW (onW w V) (onW w V)) Q := by
  have hTpos:=ha.trans_le hT
  have hPpos:=hb.trans_le hP
  have hprod : a*b≤pr w T*pr (onW w T) P:=
    mul_le_mul hT hP hb.le hTpos.le
  obtain ⟨hm,hrel⟩:=equity_trim hw T V P hsub hTpos hPpos hloss
  have hmass : a*b/2≤pr w V := by linarith only [hm,hprod,hsmall]
  refine ⟨hmass,fun Q=>?_⟩
  have herr : δ/(pr w T*pr (onW w T) P)≤δ/(a*b):=
    div_le_div_of_nonneg_left hδ (mul_pos ha hb) hprod
  have hh:=hrel ((half_pos (mul_pos ha hb)).trans_le hmass) Q
  have he:=mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ)≤2)
  simp only [mul_div_assoc] at he ⊢
  linarith only [hh,he]

/-- A fixed lower bound gives an explicit error after trimming. -/
theorem constant_mass_trim {l : Filter ℕ} (z : ℕ→ℝ) (hz : Tendsto z l atTop)
    {A : ℕ→Type} [∀ i,Fintype (A i)]
    (w : ∀ i,Wgt (A i)) (hw : ∀ᶠ i in l,∀ x,0≤w i x)
    (T V P : ∀ i,A i→Prop) {δ : ℕ→ℝ} (hδ : ExpSmall l z δ)
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hT : ∀ᶠ i in l,a≤pr (w i) (T i))
    (hP : ∀ᶠ i in l,b≤pr (onW (w i) (T i)) (P i))
    (hf : ∀ᶠ i in l,(∀ x,V i x→T i x∧P i x) ∧
      pr (w i) (fun x=>T i x∧P i x∧¬V i x)≤δ i) :
    (∀ᶠ i in l,a*b/2≤pr (w i) (V i)) ∧
    warm l z (fun i=>pr (w i) (V i)) ∧
    ExpSmall l z (fun i=>2*δ i/(a*b)) ∧
    ∀ᶠ i in l,∀ Q : A i×A i→Prop,
      pr (pairW (onW (onW (w i) (T i)) (P i)) (onW (onW (w i) (T i)) (P i))) Q
        -2*δ i/(a*b) ≤ pr (pairW (onW (w i) (V i)) (onW (w i) (V i))) Q := by
  have hab : 0<a*b/2:=half_pos (mul_pos ha hb)
  have he : ∀ᶠ i in l,δ i≤a*b/2 := (hδ.lim hz).eventually (eventually_le_nhds hab)
  have hpoint : ∀ᶠ i in l,a*b/2≤pr (w i) (V i) ∧
      ∀ Q : A i×A i→Prop,
      pr (pairW (onW (onW (w i) (T i)) (P i)) (onW (onW (w i) (T i)) (P i))) Q
        -2*δ i/(a*b) ≤ pr (pairW (onW (w i) (V i)) (onW (w i) (V i))) Q := by
    filter_upwards [hw,hT,hP,hf,he] with i hi hT hP hf he
    exact fixed_mass_trim (w i) hi (T i) (V i) (P i) a b (δ i) ha hb
      ((pr_nonneg hi).trans hf.2) he hT hP hf.1 hf.2
  refine ⟨hpoint.mono (fun _ h=>h.1),(warm.const hz hab).mono (hpoint.mono (fun _ h=>h.1)),?_,
    hpoint.mono (fun _ h=>h.2)⟩
  convert hδ.mul (expO_const hz (2/(a*b))) using 1
  funext i
  ring
end
end Lax793645Proofs.Simplifications
