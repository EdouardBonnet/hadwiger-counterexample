import Lax793645Proofs.Simplifications.GramReferenceFourier

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

def gramKeySet (E : Rail I) (Z : Vec E) (N : ℕ) : KeyCoordinates I N→Prop :=
  fun x=>traced (keyPlus x,keyMinus x) E Z

theorem gram_reference_mass (E : Rail I) (Z : Vec E) :
    |pr unif (gramKeySet E Z N)-bp (-num E)|≤bp (-(N:ℝ)/2) := by
  have hh:=gram_indicator_fourier (N:=N) E Z 0
  simpa only [linearFourier,vectorPhase,zero_dotProduct,wsign_zero,one_mul,
    eq_self_iff_true,ind_true,mul_one,gramKeySet,pr] using hh

/-- Conditioning on the prescribed Gram table retains exponentially
small bias against every nonzero linear character. -/
theorem gram_reference_bias (E : Rail I) (Z : Vec E)
    (hN : bp (-(N:ℝ)/2)≤bp (-num E)/2) :
    IsLaw (unifOn (gramKeySet E Z N)) ∧
    bp (-num E)/2≤pr unif (gramKeySet E Z N) ∧
    ∀ ξ : KeyCoordinates I N,ξ≠0 →
      |avg (unifOn (gramKeySet E Z N)) (vectorPhase ξ)|≤
        2*bp (num E)*bp (-(N:ℝ)/2) := by
  let K:=gramKeySet E Z N
  have hmass:=gram_reference_mass (N:=N) E Z
  have hlow : bp (-num E)/2≤pr unif K := by
    have hh: bp (-num E)-pr unif K≤bp (-(N:ℝ)/2):=
      (le_abs_self _).trans (by rwa [abs_sub_comm])
    linarith only [hh,hN]
  have hpos : 0<pr unif K := (half_pos (bp_pos (-num E))).trans_le hlow
  obtain ⟨x,hx,_⟩:=exists_of_pr_pos unif_law.nz hpos
  refine ⟨unifOn_law ⟨x,hx⟩,hlow,fun ξ hξ=>?_⟩
  have hh:=gram_indicator_fourier (N:=N) E Z ξ
  rw [ind_zero hξ,mul_zero,sub_zero] at hh
  have he : linearFourier (fun x=>ind (K x)) ξ=
      pr unif K*avg (unifOn K) (vectorPhase ξ) := by
    rw [←part_reset K _ hpos]
    unfold linearFourier partMean
    apply avg_congr
    intro x _
    ring
  change |linearFourier (fun x=>ind (K x)) ξ|≤_ at hh
  rw [he,abs_mul,abs_of_pos hpos] at hh
  have hscale : (bp (-num E)/2)*(2*bp (num E))=1 := by
    rw [bp_neg]
    field_simp [(bp_pos (num E)).ne']
  apply le_of_mul_le_mul_left _ (half_pos (bp_pos (-num E)))
  calc
    _≤pr unif K*|avg (unifOn K) (vectorPhase ξ)|:=
      mul_le_mul_of_nonneg_right hlow (abs_nonneg _)
    _≤bp (-(N:ℝ)/2):=hh
    _=(bp (-num E)/2)*(2*bp (num E)*bp (-(N:ℝ)/2)):=by rw [←mul_assoc,hscale,one_mul]

theorem query_gram_equivalence {p : Shape} (t : Tagging p I)
    [DecidableEq (KeySlots p t)] (q : I→F) (x : KeyCoordinates (KeySlots p t) N) :
    ownPart t q (queryFromCoordinates t N x)↔
      gramKeySet (crowded (ownPort t)) (directions (ownPort t) (ownMap t q)) N x := by
  rw [gramKeySet,match_crowd]
  simp only [ownPart,queryFromCoordinates,Equiv.apply_symm_apply]

end
end Lax793645Proofs.Simplifications
