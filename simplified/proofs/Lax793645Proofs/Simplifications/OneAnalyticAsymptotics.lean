import Lax793645Proofs.Simplifications.OneAnalyticParameters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters StatusAnalysis Filter Function
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {M s0:ℕ} {q:PreparationParameters} {l:Filter ℕ}
  {m:cycleM p} {s:OneRhythms p M} {w:OneTale p M}

theorem OneVeil.score_cost (h:OneVeil p M q s0 l m s w)
    (v:OneStations p M (onePreparationPins q) s):
    ∃ δ:ℕ→ℝ,ExpSmall l (fun n=>((2*(M*n):ℕ):ℝ)) δ ∧
      ∀ᶠ n in l,∀ (Q:Format) (d e:Rates) (x:Typus p Q d e)
        (k:Fin (2^oneDeckMax p (onePreparationPins q))),
        (v n).arena x (m n) (w n) k≤δ n := by
  let N (n:ℕ):=M*n
  let z (n:ℕ):ℝ:=(2*N n:ℕ)
  have hz:Tendsto z l atTop:=(one_trend_sizes l h.time h.parameters.planted.hM).2
  let C n:=((s n).amount (w n))⁻¹
  have hc:=h.durable.mass.inv_cap
  let δ n:=bp (-1*z n)*C n*C n+bp (-0.005*z n)*2
  have hd:ExpSmall l z δ:=
    (((ExpSmall.bp_n zero_lt_one).mul hc).mul hc).add hz
      ((ExpSmall.bp_n (by norm_num)).mul (expO_const hz _))
  refine ⟨δ,hd,?_⟩
  filter_upwards [h.moment,h.durable.mass.positive,h.durable.shape,
    h.parameters.secure.filter_mono h.time] with n hn hmass hs he Q d e x k
  have hm:=hn.1.law
  let u:=(s n).sap (w n)
  have hu:IsLaw u:=(s n).sap_law hmass hm
  have hk i:u i≤C n*w n i:=ImageLeafMixture.upper_sap hm hmass i
  have hpair (x:OneUnit p n (N n)×OneUnit p n (N n)):
      pairW u u x≤(C n*C n)*pairW (w n) (w n) x:=
    (mul_le_mul (hk _) (hk _) (hu.nz _) ((hu.nz _).trans (hk _))).trans_eq
      (by unfold pairW; ring)
  have hf:pr (pairW u u) (oneClash (m n))≤(C n*C n)*bp (-200*z n):=
    (pr_cap hpair _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [z,N,Nat.cast_mul,Nat.cast_ofNat] using hn.2.2.2.le) (mul_self_nonneg _))
  refine ((v n).arena_bound x _ _ k hs.1 hm hmass he).trans ?_
  change _≤δ n
  unfold δ
  apply add_le_add _ (by dsimp [z,N]; push_cast; ring_nf; exact le_rfl)
  calc
    _≤oneBeamPrice p (N n)*((C n*C n)*bp (-200*z n)):=
      mul_le_mul_of_nonneg_left hf (bp_pos _).le
    _=(oneBeamPrice p (N n)*bp (-200*z n))*(C n*C n):=by ring
    _≤bp (-z n)*(C n*C n):=mul_le_mul_of_nonneg_right
      (by simpa only [z,N,Nat.cast_mul,Nat.cast_ofNat] using one_beam_cost p (N n))
      (mul_self_nonneg _)
    _=bp (-1*z n)*C n*C n:=by rw [neg_one_mul]; ring

/-- Both caps are charged in the prepared mixed law, before any separate
leaf normalization or compatible-pair restriction. -/
theorem OneVeil.query_caps (h:OneVeil p M q s0 l m s w):
    ∀ᶠ n in l,let u:=(s n).sap (w n);
      IsLaw u ∧ oneBySide u (m n) (bp ((1/32:ℝ)*n)) ∧
        ∀ x,u x≤bp (q.spJoint*(2*(M*n):ℝ))*oneUnitRaw (m n) (M*n) x := by
  let z (n:ℕ):ℝ:=(2*(M*n):ℕ)
  have hz:Tendsto z l atTop:=(one_trend_sizes l h.time h.parameters.planted.hM).2
  have hM:(1:ℝ)≤M:=by exact_mod_cast h.parameters.planted.hM
  let e:ℝ:=1/(256*M)
  have he:0<e:=by dsimp [e]; positivity
  let D n:=((s n).amount (w n))⁻¹
  filter_upwards [h.moment,h.durable.mass.inv_cap e he,h.durable.mass.positive,
    expO_const hz q.L e he] with n hn hc hp hL
  let u:=(s n).sap (w n)
  have h1 i:u i≤D n*w n i:=ImageLeafMixture.upper_sap hn.1.law hp i
  have hD:0≤D n:=(inv_pos_of_pos hp).le
  have hB:D n*q.L≤bp ((1/32:ℝ)*n):=by
    have hi:e*z n=(1/128:ℝ)*n:=by
      dsimp [e,z]; push_cast; field_simp; ring
    calc
      _≤bp (e*z n)*bp (e*z n):=mul_le_mul
        ((le_abs_self _).trans hc) ((le_abs_self _).trans hL)
        h.parameters.planted.early.hL (bp_pos _).le
      _≤_:=by
        rw [←bp_add,hi]
        apply bp_le
        linarith only [Nat.cast_nonneg (α:=ℝ) n]
  refine ⟨(s n).sap_law hp hn.1.law,one_upper_side hn.1.border h1 hD hB,fun x=>?_⟩
  apply ((h1 x).trans (mul_le_mul_of_nonneg_left (hn.1.total x) hD)).trans
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (prodW_nonneg (fun _=>one_raw_nonneg (m n)) x)
  refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hc) (bp_pos _).le).trans ?_
  rw [←bp_add]
  apply bp_le
  have he1:e≤1:=by dsimp [e]; exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  unfold PreparationParameters.spJoint
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_right he1
    (show 0≤2*((M:ℝ)*n) from by positivity)]

end
end Lax793645Proofs.Simplifications
