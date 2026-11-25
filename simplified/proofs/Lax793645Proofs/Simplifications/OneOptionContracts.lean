import Lax793645Proofs.Simplifications.OneQueryHistograms
import Lax793645Proofs.Simplifications.OneScriptRealization
import Lax793645Proofs.Simplifications.OneUnaryRecords
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CompatibleOptionRealization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneOptions
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates} {side : Bool}

def signed (w : Quill p q d side) (t : Tagging p (Messenger q))
    (x y : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (s : Charts p n d) (T : OneCross p n) (K : ℕ) :=
  oneCharted s x.sp ∧ OnePenSpace (w.pen t) x.sp K ∧
    oneStill side w.amp s T ∧ oneTableSafe x.sp y.sp T

def chances (w : Typus p q d e) (s : Charts p n d) (v : Charts p n e)
    (x y : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (T : OneCross p n) (K : ℕ) :=
  (onePermission w) ∧ signed w.qA w.t x y s T K ∧
    signed w.qB w.t y x v (fun e=>(T e)ᵀ) K

def notified (m : Mixer p n) (x y : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (T : OneCross p n) (C : Prop) (o : OneUnit p n N) :=
  C ∧ imagePinAgree oneCoordinateImages x o ∧
    (∀ i,oneFrameLaw m (o i)) ∧ oneTableFlag x y T o

def ticket (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (T : OneCross p n)
    (x y : OneUnit p n N) :=
  oneTableSafe a.sp b.sp T ∧ oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ) ∧
    oneFitsTable a.sp b.sp T (oneCrossMatrix x y)

theorem ticket_flags (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (T : OneCross p n)
    (x y : OneUnit p n N) (h : ticket a b T x y)
    (hx : imagePinAgree oneCoordinateImages a x) (hy : imagePinAgree oneCoordinateImages b y) :
    oneTableFlag a b T x ∧ oneTableFlag b a (fun e=>(T e)ᵀ) y := by
  have hfit:=one_fits_table_reciprocal a.sp b.sp T (oneCrossMatrix x y) h.2.2
  simp_rw [one_cross_reciprocal] at hfit
  exact ⟨one_table_flag_fits a b T _ h.2.2 x (one_table_flag_actual a b x y hy),
    one_table_flag_fits b a _ _ hfit y (one_table_flag_actual b a y x hx)⟩

/-- The same finite scalar system supplies scripts for the single-frame
construction. Its target uses the quadratic channel contract. -/
theorem optionVia (q : Format) (d e : Rates)
    (s t : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (T : OneCross p n) (K : ℕ)
    (ha : oneTableSafe s.sp t.sp T) (hb : oneTableSafe t.sp s.sp (fun e=>(T e)ᵀ))
    (tags : Tagging p (Messenger q)) (x : Charts p n d) (y : Charts p n e)
    (hx : oneCharted x s.sp) (hy : oneCharted y t.sp)
    (f : Fabric p q d true) (g : Fabric p q e false)
    (hf : OnePenSpace ((f.hang 0).pen tags) s.sp K)
    (hg : OnePenSpace ((g.hang 0).pen tags) t.sp K)
    (z : Messenger q→F) (hF : f.up tags z) (hG : g.up tags z)
    (hj : 1≤p.J) (h2 : 3≤p.g) (hodd : Odd p.g) (h₀ : ∀ i,1≤q i ∧ q i≤7)
    (he : speak _ _ (sendSum z f.amp g.amp)=(oneHailing x y T,0)) :
    ∃ (a b : Script p (Messenger q)),chances ⟨tags,z,f.hang a,g.hang b⟩ x y s t T K := by
  obtain ⟨hQ,hR,hL,hS⟩:=(one_spoken x y T z f.amp g.amp).mp he
  obtain ⟨a,ha'⟩:=one_proclaim_script true f.amp g.amp tags hR (fun i=>(h₀ i).1) hS.2 h2 hodd hj
  have hh : rhyme g.amp f.amp:=fun i=>(add_comm ..).trans (hR i)
  obtain ⟨b,hb'⟩:=one_proclaim_script false g.amp f.amp tags hh (fun i=>(h₀ i).1) hL.2 h2 hodd hj
  exact ⟨a,b,⟨h₀,hF,hG,hQ,hR,ha',hb'⟩,⟨hx,hf,hL,ha⟩,⟨hy,hg,hS,hb⟩⟩

end OneOptions
end
end Lax793645Proofs.Simplifications
