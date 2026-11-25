import Lax793645Proofs.Simplifications.OneCellPositivityScales
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalSignaturePositivity

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Appearance Template Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N K r d : ℕ}
namespace OneAppearance
variable (x : Appearance p) (Y : OneSilhouette p N r)

theorem oneSmudges (o : OneUnit p n N) (m:Mixer p n) (v : Ax p n d) (i:Nodes) (j : Knobs p.g n) :
    (oneProfile x i o m v j).2.1=((scan p x.l x.f j).diagO,stains x.trot m v j) := by
  apply Prod.ext
  · exact role_scan p _ _ _ _
  funext i; exact T_swap m _ _


set_option maxHeartbeats 800000 in
theorem oneDemonstrates (o : OneUnit p n N) {m : Mixer p n}
    (v : Ax p n d) (K:ℕ) (i:Nodes) (j:Fin r) (δ : ℝ) (hd:0<δ)
    (z : Digest p.g) (u:Cell d)
    (he : z.feasible x.l x.f) (hf : z.sumBit=x.q) (ht : 1≤p.r) (hn : 2*p.r≤n)
    (hh : δ≤ oneReference x Y j)
    (hs : oneSmoothSilk p δ δ Y m K (o i)) (hK : d≤K^2)
    (hV : Injective v) (hv : ∀ x,totalRank (v x) ≤ K) :
    basebeta p K/2 ≤ pr (oneReflected x Y i o m v j) (nearly p z (z.diagO,u)) := by
  classical
  have ha : x.apt := ⟨z,he,hf⟩
  let μ:= oneReference x Y j
  let f := o i
  obtain ⟨hM,hB⟩:= hs x
  specialize hM ha
  specialize hB z j he hf hh
  let U (y:OneAtomKey (p:=p) (x.trot.t ()) N) := Y x.l x.q y=j
  have hm : basebeta p K*μ ≤
      pr (x.wit n) (fun y=> (scan p x.l x.f y=z∧Y x.l x.q (oneFace x f y)=j) ∧
        stains x.trot m v y=u) := by
    let h := one_patrol_beta x.trot U m K z he ht hn f
    dsimp only at h
    rw [hf] at h
    exact h hB d hK v hV hv u
  let w := nearly p z (z.diagO,u)
  have hq (y : Knobs p.g n) :
      (scan p x.l x.f y=z ∧ Y x.l x.q (oneFace x f y)=j) ∧ stains x.trot m v y=u →
        oneShowTag x Y (o i) y=j∧ w (oneProfile x i o m v y) := by
    rintro ⟨⟨h,h1⟩,h2⟩
    refine ⟨h1,h,?_⟩; rw [oneSmudges,h,h2]
  have hW := Appearance.witLaw ha ht hn
  have heq := (hm.trans (pr_mono hW.nz hq)).trans_eq (oneShow_pr x Y i o m v hW j w)
  let ν:= oneEmpirical x Y f j
  have h2 : ν ≤ 2*μ := by
    have hz : |μ-ν|≤δ := le_trans
      (Finset.single_le_sum (fun k _ => abs_nonneg (oneReference x Y k-oneEmpirical x Y f k))
        (Finset.mem_univ j)) hM
    change δ≤ μ at hh
    linarith [(abs_le.mp hz).1]
  let Q := pr (oneReflected x Y i o m v j) w
  have h3 : basebeta p K*μ≤ ν*Q := heq
  have ht := mul_le_mul_of_nonneg_right h2
    (show 0≤ Q from pr_nonneg (oneReflectedLaw x Y hW i o m v j).nz)
  apply le_of_mul_le_mul_right _ (hd.trans_le hh)
  change _*μ ≤ Q*μ
  linarith only [h3,ht]

theorem oneRawink (x : Appearance p) (m : Mixer p n) (i : Nodes) (o : OneUnit p n N)
    (v : Ax p n d) :
    carried (x.wit n) (x.fitsink ∘ oneProfile x i o m v) := by
  let w:=x.wit n
  have hC : carried w (fun y=>dialed p x.l x.f y=x.q) :=
    normW_carried (subW_carried (spins p n) _)
  intro y hi
  refine hC y (fun h=>?_); apply hi
  refine ⟨?_,h, (role_scan p _ _ _ _).symm⟩
  intro j hj
  unfold oneProfile oneSpecify; change scan p x.l x.f y j=0
  unfold scan
  simp [hj]
theorem oneRefInk (i : Nodes) (o : OneUnit p n N) (m:Mixer p n) (v : Ax p n d)
    (j:Fin r) : carried (oneReflected x Y i o m v j) x.fitsink :=
  oneReflection_exact x Y i o m v j _ (oneRawink x m i o v)

end OneAppearance
end
end Lax793645Proofs.Simplifications
