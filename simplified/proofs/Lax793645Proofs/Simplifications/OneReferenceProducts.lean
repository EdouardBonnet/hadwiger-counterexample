import Lax793645Proofs.Simplifications.OneKeyReferenceLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
set_option maxHeartbeats 600000 in
theorem one_reference_product (t : Tagging p I) (q : I → F)
    (f : ∀ i,Wgt (OneAtomKey (p:=p) (t i) N))
    (hf : ∀ i x,|f i x|≤1) (hN : 2*num (I×Toast p)+2≤(N:ℝ)) :
    |avg (oneLawNu p N t q) (prodW f)- ∏ i,avg (oneLawOmega p N (t i) (q i)) (f i)|≤
      2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  classical
  let F (i : I) := (f i)∘(oneMug p (t i) N).symm
  let g := trayPort p t
  let A := trayMap p t q
  have hpL i := show 2*num (Port g i)+2≤(N:ℝ) by linarith only [hN,port_limit g i]
  have he :
      avg (quadraticWave A N) (brightProd F) =avg (oneLawNu p N t q) (prodW f) := by
    unfold A; rw [←one_law_tray,mapW_avg]
    have hh x : brightProd F (oneTray p t N x)=prodW f x := by
      simp_rw [brightProd,one_tray_sips,F,Function.comp_apply,Equiv.symm_apply_apply]
      rfl
    simp_rw [hh]
  have hw i : avg (quadraticWave (laneM A i) N) (F i)=avg (oneLawOmega p N (t i) (q i)) (f i) := by
    unfold A; rw [←one_law_mug,mapW_avg]
    simp_rw [F,Function.comp_apply, Equiv.symm_apply_apply]
  have h := quadratic_compare_waves A F (fun i x => hf _ _) hpL
  simp_rw [he,hw] at h; exact h


theorem one_price_nu (t : Tagging p I) (q : I→F)
    (hN : 2*num (I×Toast p)+2≤(N:ℝ)) :
    (quadraticNetFact (trayPort p t))⁻¹≤pr unif (oneOwnKeyPart t q (N:=N)) := by
  let g:=trayPort p t
  have hpL i : 2*num (Port g i)+2≤(N:ℝ):=by linarith only [hN,port_limit g i]
  have he : pr unif (quadraticWavePart (trayMap p t q) (N:=N))=
      pr unif (oneOwnKeyPart t q (N:=N)) := by
    rw [←unif_equiv (oneTray p t N),mapW_pr]
    congr 1
    funext x
    exact propext (one_tray_wave t q x).symm
  rw [←he]
  exact quadratic_wave_norm g _ hpL

theorem one_nu_law (t : Tagging p I) (q : I→F)
    (hN : 2*num (I×Toast p)+2≤(N:ℝ)) : IsLaw (oneLawNu p N t q) := by
  rw [oneLawNu,←on_unif]
  exact on_law unif_law.nz ((inv_pos_of_pos (quadratic_net_fact_pos _)).trans_le
    (one_price_nu t q hN))

theorem one_omega_law (l : Tag p.g) (q : F) (hN : 2*num (Toast p)-(N:ℝ)≤ -1) :
    IsLaw (oneLawOmega p N l q):=mapW_law (omegaLaw p l q hN) _

end
end Lax793645Proofs.Simplifications
