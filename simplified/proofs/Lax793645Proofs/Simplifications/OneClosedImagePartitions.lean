import Lax793645Proofs.Simplifications.OneClosedPinLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

/-- The actual single-frame raw law supplies the closed-pin peeling
hypothesis. The output retains the requested spreading exponent ζ. -/
theorem one_closed_image_partition (m : Mixer p n)
    {w : Wgt (OneUnit p n N)} {D ζ : ℝ} (hz : 0<ζ) (hz' : ζ<1)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hroom : (dim (OneFull p n):ℝ)+2≤((ζ/6)/4)*(2*N))
    (hcap : ∀ x,w x≤bp (D*(2*N))*oneUnitRaw m N x) (hw : ∀ x,0≤w x)
    (R : Finset (OneUnit p n N)) (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (ha : (onePinClosure p n).close a.sp=a.sp)
    (hf : ∀ x∈R,imagePinAgree oneCoordinateImages a x)
    {K : ℕ} (hK : D+ζ≤((ζ/6)-(ζ/6)/4)*K) :
    ∃ G : Finset (Finset (OneUnit p n N)),
      (∀ S∈G,S⊆R ∧ ∃ b,ClosedImageCell oneCoordinateImages (onePinClosure p n)
        w (oneUnitRaw m N) D ζ K S a b) ∧
      (∀ x,∀ S∈G,∀ J∈G,x∈S→x∈J→S=J) ∧
      pr w (fun x=>x∈R ∧ ¬∃ S∈G,x∈S)≤bp (-ζ*(2*N)) := by
  have hn : 0<2*N:=by omega
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    closed_image_partition oneCoordinateImages (by decide : 1≤6) (onePinClosure p n)
      hz hz' hn (fun b hb=>one_closed_pin_cap m b hb (by linarith) hN hroom)
      (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcap) hw R a ha hf hK

end
end Lax793645Proofs.Simplifications
