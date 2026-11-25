import Lax793645Proofs.Simplifications.OneCoverSeparation
import Lax793645Proofs.Simplifications.OnePhaseAlternativeSupport

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}

def oneSeparated (x : OneUnit p n N) (S : SymCover p (2*N)) : Prop:=
  ∀ i e,Disjoint (S e) (onePrimalImages x i e)

def oneScaleBill (p : Shape) (n N d : ℕ) (H : ℝ):=
  2*num (Comp p.g)*H*bp (num (Row p n)+d+3-2*(N:ℝ))

theorem one_cover_separation_failure {w : Wgt (OneUnit p n N)} {H : ℝ}
    (hw : SubLaw w) (m : Mixer p n) (hH : 0≤H)
    (hside : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 5≤N)
    (S : SymCover p (2*N)) (d : ℕ) (hd : oneCoverDimension S≤d) :
    pr w (fun x=>¬oneSeparated x S)≤oneScaleBill p n N d H := by
  classical
  let E (z : Bool×Comp p.g) (x : OneUnit p n N):=
    ¬Disjoint (onePrimalImages x z.1 z.2) (S z.2)
  have he x : ¬oneSeparated x S→∃ z,E z x := by
    simp only [oneSeparated,not_forall]
    rintro ⟨i,e,h⟩
    exact ⟨(i,e),fun hh=>h hh.symm⟩
  refine ((pr_mono hw.nz he).trans (pr_exists_le hw.nz E)).trans ?_
  have hb (z : Bool×Comp p.g) :
      pr w (E z)≤H*bp (num (Row p n)+d+3-2*(N:ℝ)) := by
    refine (one_unit_cover_component m z.1 hH hw (hside z.1) hroom hN z.2 (S z.2)).trans ?_
    apply mul_le_mul_of_nonneg_left (bp_le ?_) hH
    have hh : dim (S z.2)≤d:=
      (Finset.single_le_sum (fun e _=>Nat.zero_le (dim (S e))) (Finset.mem_univ z.2)).trans hd
    have hc : (dim (S z.2):ℝ)≤d:=by exact_mod_cast hh
    linarith only [hc]
  refine (Finset.sum_le_sum (fun z _=>hb z)).trans_eq ?_
  simp [oneScaleBill,num,Finset.sum_const,Fintype.card_prod]
  ring

set_option maxHeartbeats 800000 in
/-- The symmetric records are selected from actual marked profiles.
There is no assumed record decoder or phase-decomposition oracle. -/
theorem one_marked_bazaar (marks : OneUnit p n N→Bool→Profile p n)
    (w : Wgt (OneUnit p n N)) (S : SymCover p (2*N))
    (hmarks : ∀ x,w x≠0→∀ i,marks x i∈Xspace p n)
    (hsep : ∀ x,w x≠0 → oneSeparated x S)
    (hcover : ∀ x,w x≠0 → oneSymCovered S (oneMarkedDelta x (marks x)))
    (hne : ∀ x,w x≠0 → oneMarkedDelta x (marks x)≠0)
    (hr : ∀ x,w x≠0→totalRank (marks x true)≤r) :
    ∃ s : OneBazaar p n r S,s.opened (fun x=>oneMarkedDelta x (marks x)) w := by
  classical
  have hex x : ∃ X : SymAtlas p r S,w x≠0→symStandard X ∧
      ∀ i,∃ Z,symCompFor X Z (onePrimalImages x i) (oneMarkedDelta x (marks x)) := by
    by_cases hx : w x=0
    · exact ⟨default,fun h=>False.elim (h hx)⟩
    have hc : ∀ e,vanish (S e) (S e) (oneMarkedDelta x (marks x) e):=
      (covered_iff (oneSymCov S) (oneMarkedDelta x (marks x))).mp (hcover x hx)
    obtain ⟨X,hX⟩:=one_marked_offsets (r:=r) x (marks x) (hmarks x hx) S (hsep x hx)
      hc (hne x hx) (hr x hx)
    exact ⟨X,fun _=>hX⟩
  choose ix hix using hex
  choose bag hbag using
    show ∀ (M : SymAtlas p r S) (i : Bool) (x),∃ Z,
        M=ix x→w x≠0→symCompFor M Z (onePrimalImages x i) (oneMarkedDelta x (marks x)) from by
      intro M i x
      by_cases hx : w x=0
      · exact ⟨0,fun _ h=>False.elim (h hx)⟩
      by_cases hm : M=ix x
      · subst M
        obtain ⟨Z,hZ⟩:=(hix x hx).2 i
        exact ⟨Z,fun _ _=>hZ⟩
      exact ⟨0,fun h=>False.elim (hm h)⟩
  exact ⟨⟨ix,bag⟩,fun x hx=>⟨(hix x hx).1,fun i=>hbag _ i x rfl hx⟩⟩

end
end Lax793645Proofs.Simplifications
