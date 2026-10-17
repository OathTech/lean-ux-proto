import Leanux.Proofs.WG.Config.MixedDumpModel
import Leanux.Proofs.WG.Config.Returns
import Leanux.Proofs.WG.Config.Validation

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual read and serialization return for every stored width and room.
A short put restores the original skb; all branch records remain actual. -/
theorem readNode_getAllowedips_returns (n : AipNode) (skb : NlSkb) (P : WGWorld → Prop) :
    Returns (do let (family,masked,cidr) ← readNode n; getAllowedips skb family masked cidr)
      P (fun result g => P g ∧ result =
        if dumpNodeSpace n ≤ skb.room then
          ({skb with room := skb.room - dumpNodeSpace n},some (dumpNodeJson n)) else (skb,none)) := by
  intro g ambient pre
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site,outcome := value,netRx := a.netRxSection}}
  let swapped := if n.bitlen = 32 then mark ambient .swapEndian32 (n.bitlen == 32)
    else mark (mark ambient .swapEndian32 (n.bitlen == 32)) .swapEndian128 (n.bitlen == 128)
  let before := mark swapped .readNodeHasCidr (n.cidr != 0)
  let family := if n.bitlen = 32 then 4 else 6
  let masked := if n.cidr = 0 then 0 else n.bits / 2 ^ (n.bitlen - n.cidr) * 2 ^ (n.bitlen - n.cidr)
  have readRun : ((readNode n).run g).run ambient = .ok (((family,masked,n.cidr),g),before) := by
    by_cases width : n.bitlen = 32 <;> by_cases zero : n.cidr = 0
    all_goals simp [readNode,swapEndian,width,zero,branch,AmbientM.branch,swapped,before,mark,family,masked]
    all_goals rfl
  have cost : allowedIpSpace family = dumpNodeSpace n := by
    by_cases width : n.bitlen = 32 <;> simp [family,dumpNodeSpace,allowedIpSpace,nlaTotal,width]
  have json : Json.mkObj [("family",toJson family),
      ("addr",toJson (hexBE masked (if family = 6 then 16 else 4))),("cidr",toJson n.cidr)] = dumpNodeJson n := by
    by_cases width : n.bitlen = 32 <;> simp [family,masked,dumpNodeJson,width]
  have serial : ∃ after, ((getAllowedips skb family masked n.cidr).run g).run before =
      .ok (((if dumpNodeSpace n ≤ skb.room then
        ({skb with room := skb.room - dumpNodeSpace n},some (dumpNodeJson n)) else (skb,none)),g),after) := by
    have positive : 28 ≤ dumpNodeSpace n := by unfold dumpNodeSpace; split <;> omega
    by_cases nest : skb.room < 4
    · have short : ¬ dumpNodeSpace n ≤ skb.room := by omega
      refine ⟨mark before .getAipNoNest true,?_⟩
      simp [getAllowedips,NlSkb.put,nlaTotal,nest,short,branch,AmbientM.branch,mark]
      rfl
    · let a0 := mark before .getAipNoNest false
      by_cases cidrRoom : skb.room - 4 < 8
      · have short : ¬ dumpNodeSpace n ≤ skb.room := by omega
        refine ⟨mark a0 .getAipPutCidr true,?_⟩
        simp [getAllowedips,NlSkb.put,nlaTotal,nest,cidrRoom,short,branch,AmbientM.branch,a0,mark]
        rfl
      · let a1 := mark a0 .getAipPutCidr false
        by_cases familyRoom : skb.room - 12 < 8
        · have short : ¬ dumpNodeSpace n ≤ skb.room := by omega
          refine ⟨mark a1 .getAipPutFamily true,?_⟩
          simp [getAllowedips,NlSkb.put,nlaTotal,nest,cidrRoom,familyRoom,short,Nat.sub_sub,
            branch,AmbientM.branch,a1,a0,mark]
          rfl
        · let a2 := mark (mark a1 .getAipPutFamily false) .getAipFamily6 (family == 6)
          by_cases addressRoom : skb.room - 20 < nlaTotal (if family = 6 then 16 else 4)
          · simp only [nlaTotal] at addressRoom
            have short : ¬ dumpNodeSpace n ≤ skb.room := by
              simp only [allowedIpSpace,nlaTotal] at cost
              omega
            refine ⟨mark a2 .getAipPutAddr true,?_⟩
            simp [getAllowedips,NlSkb.put,nlaTotal,nest,cidrRoom,familyRoom,short,Nat.sub_sub,
              branch,AmbientM.branch,a2,a1,a0,mark,addressRoom]
            rfl
          · simp only [nlaTotal] at addressRoom
            have fits : dumpNodeSpace n ≤ skb.room := by
              simp only [allowedIpSpace,nlaTotal] at cost
              omega
            refine ⟨mark a2 .getAipPutAddr false,?_⟩
            simp [getAllowedips,NlSkb.put,nlaTotal,nest,cidrRoom,familyRoom,fits,Nat.sub_sub,
              branch,AmbientM.branch,a2,a1,a0,mark,addressRoom]
            rw [← cost,← json]
            simp [allowedIpSpace,nlaTotal,Nat.add_assoc]
            rfl
  obtain ⟨after,serialRun⟩ := serial
  refine ⟨_,g,after,?_,pre,rfl⟩
  change (((readNode n).run g).run ambient >>= _) = _
  rw [readRun]
  exact serialRun

end Leanux.Proofs.WG.Config
