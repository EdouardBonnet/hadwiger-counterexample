import Lax793645Proofs.Simplifications.OneOrientationRankBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BasisConditioning

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Template Finset Matrix Function LinearMap Module Submodule Filter Real
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneLuminous (v : Template.Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n)) (D : OneAtomKey (p:=p) (v.t ())
    N →Prop) (K : ℕ) (i : OneOrient p n N) :=
  let P := oneOffBeat v D i
  0<pr w P ∧ ∀ (d : ℕ), d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
    Injective f → (∀ x,totalRank (f x)≤K) → ∀ x,
    (7/8:ℝ)*bp (-(d:ℝ)) ≤ pr (onW w P) (fun z=> stains v m f z=x)

set_option maxHeartbeats 800000 in
theorem one_glow_luminous (v : Template.Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (hw : IsLaw w)
    (S : OneAtomKey (p:=p) (v.t ()) N → Prop)
    (K : ℕ) (i : OneOrient p n N) (δ : ℝ) (hδ : 0<δ) (he : δ ≤ pr w (oneOffBeat v S i))
    (h : ∀ x, 0<totalRank x → totalRank x≤K → ¬ oneRankGlow v m w S (glintRate K) δ x i) :
    oneLuminous v m w S K i := by
  classical
  let P := oneOffBeat v S i
  have hP : 0<pr w P := hδ.trans_le he
  let u := onW w P; have hu : IsLaw u := on_law hw.nz hP
  refine ⟨hP,fun d hd f hf hg x => ?_⟩
  let s := stains v m f
  have heq :
      pr u (fun z => s z=x) = avg unif (fun i => vectorPhase i x*
          avg u (fun z => vectorPhase i (s z))) := by
    unfold pr
    simp_rw [vector_expand]
    rw [avg_avg]
    apply avg_congr
    intro i hi
    rw [avg_mul]; ring
  let b := bp (-(d:ℝ))
  let Q (k : Vec (Fin d)) := vectorPhase k x * avg u (fun z => vectorPhase k (s z))
  have hb : 0 < b := bp_pos _
  have hh k : ind (k=0)-b/8 ≤ Q k := by
    by_cases hk : k=0
    · subst k
      have hQ : Q 0=1 := by unfold Q; simp only [vectorPhase,zero_dotProduct,wsign_zero,one_mul,
        hu.avg_const]
      rw [ind_one (show (0:Vec (Fin d))=0 from rfl),hQ]; linarith
    let k' := f k
    have hT := h k' (totalRank_pos (hf.ne hk |>.trans_eq (map_zero f))) (hg k)
    have hz : |zsumPeak p w (v.shanty m k') P| ≤ (glintRate K)*pr w P :=
      le_of_lt (lt_of_not_ge (fun h => hT ⟨he,h⟩))
    have ht :
        avg u (fun z => vectorPhase k (s z))=
          zsumPeak p w (v.shanty m k') P/pr w P := by
      unfold s u onW; simp_rw [staining]; rw [avg_norm,subW_tot]
      congr 1; simp [zsumPeak,avg,subW,mul_assoc,k']
    have h1 : |Q k|≤b/8 := by
      unfold Q; rw [ht,abs_mul,vectorPhase,wsign_abs,one_mul,abs_div,abs_of_pos hP]
      refine le_trans ((div_le_iff₀ hP).mpr hz) ((glint_within hd).trans_eq (by unfold b; ring))
    rw [ind_zero hk,zero_sub]; exact (abs_le.mp h1).1
  have h0 : unif (0:Vec (Fin d))=b := by
    unfold b; rw [unif_apply,card_space,dim_vec,bp_neg,Fintype.card_fin]
  change _ ≤ pr u (fun z => s z=x)
  rw [heq]
  refine le_trans ?_ (avg_mono unif_law.nz hh)
  rw [avg_sub,unif_law.avg_const,
    show avg unif (fun i : Vec (Fin d)=> ind (i=0))=b from (pr_point' unif _).trans h0]
  change 7/8*b≤_
  linarith
end
end Lax793645Proofs.Simplifications
