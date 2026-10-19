import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Receive

/-! Original byte/header inspection leaves preserve the native WG world.
Their branch records and Stops retain unrestricted Ambient inputs and outputs. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem validateHeaderLen_sameWGWorld (msg : List UInt8) :
    SameView (id : WGWorld → WGWorld) (validateHeaderLen msg) := by
  have hb (d : Decision) (b : Bool) : SameView (id : WGWorld → WGWorld) (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => w = initial)
  have hand (a b : WG.M Bool)
      (ha : SameView (id : WGWorld → WGWorld) a)
      (hb : SameView (id : WGWorld → WGWorld) b) :
      SameView (id : WGWorld → WGWorld) (WG.andM a b) := by
    unfold WG.andM
    apply SameView.bind ha
    intro result
    split
    · exact hb
    · exact SameView.pure _ _
  unfold validateHeaderLen
  apply SameView.bind (hb _ _)
  intro short
  split
  · exact SameView.pure _ _
  · dsimp only
    apply SameView.bind (hand _ _ (hb _ _) (hb _ _))
    intro test0
    split
    · exact SameView.pure _ _
    · apply SameView.bind (hand _ _ (hb _ _) (hb _ _))
      intro test1
      split
      · exact SameView.pure _ _
      · apply SameView.bind (hand _ _ (hb _ _) (hb _ _))
        intro test2
        split
        · exact SameView.pure _ _
        · apply SameView.bind (hand _ _ (hb _ _) (hb _ _))
          intro test3
          split
          · exact SameView.pure _ _
          · exact SameView.pure _ _

theorem prepareSkbHeader_sameWGWorld (msg : List UInt8) :
    SameView (id : WGWorld → WGWorld) (prepareSkbHeader msg) := by
  have hb (d : Decision) (b : Bool) : SameView (id : WGWorld → WGWorld) (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => w = initial)
  have hand (a b : WG.M Bool)
      (ha : SameView (id : WGWorld → WGWorld) a)
      (hb : SameView (id : WGWorld → WGWorld) b) :
      SameView (id : WGWorld → WGWorld) (WG.andM a b) := by
    unfold WG.andM
    apply SameView.bind ha
    intro result
    split
    · exact hb
    · exact SameView.pure _ _
  have hor (a b : WG.M Bool)
      (ha : SameView (id : WGWorld → WGWorld) a)
      (hb : SameView (id : WGWorld → WGWorld) b) :
      SameView (id : WGWorld → WGWorld) (WG.orM a b) := by
    unfold WG.orM
    apply SameView.bind ha
    intro result
    split
    · exact SameView.pure _ _
    · exact hb
  unfold prepareSkbHeader
  apply SameView.bind (hand _ _ (hb _ _) (hb _ _))
  intro protocol
  apply SameView.bind (hor _ _ (hb _ _) (hor _ _ (hb _ _) (hb _ _)))
  intro bad
  split
  · exact SameView.pure _ _
  · apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
    intro offset
    split
    · exact SameView.pure _ _
    · apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
      intro length
      split
      · exact SameView.pure _ _
      · apply SameView.bind (hor _ _ (hb _ _) (hb _ _))
        intro pull
        split
        · exact SameView.pure _ _
        · apply SameView.bind (hb _ _)
          intro mismatch
          split
          · exact SameView.pure _ _
          · apply SameView.bind (validateHeaderLen_sameWGWorld msg)
            intro header
            apply SameView.bind (hb _ _)
            intro missing
            split
            · exact SameView.pure _ _
            · apply SameView.bind (hb _ _)
              intro failed
              split <;> exact SameView.pure _ _

theorem ipTunnelGetDsfield_sameWGWorld (protocol : Nat) (hdr : List UInt8) :
    SameView (id : WGWorld → WGWorld) (ipTunnelGetDsfield protocol hdr) := by
  have hb (d : Decision) (b : Bool) : SameView (id : WGWorld → WGWorld) (branch d b) :=
    fun initial => hoare_liftAmbient (AmbientM.branch d b) (fun w => w = initial)
  have hu : SameView (id : WGWorld → WGWorld)
      (unsupported "a VLAN-tagged skb" : WG.M Unit) :=
    fun initial => hoare_liftAmbient (AmbientM.unsupported "a VLAN-tagged skb")
      (fun w => w = initial)
  have tail : SameView (id : WGWorld → WGWorld) (do
      if ← branch .dsfieldIp (protocol == ETH_P_IP) then return (hdr.getD 1 0).toNat
      if ← branch .dsfieldIpv6 (protocol == ETH_P_IPV6) then
        return ((hdr.getD 0 0).toNat * 256 + (hdr.getD 1 0).toNat) / 16 % 256
      return 0 : WG.M Nat) := by
    apply SameView.bind (hb _ _)
    intro ipv4
    split
    · exact SameView.pure _ _
    · apply SameView.bind (hb _ _)
      intro ipv6
      split <;> exact SameView.pure _ _
  unfold ipTunnelGetDsfield
  apply SameView.bind (hb _ _)
  intro vlan
  split
  · exact SameView.bind hu (fun _ => tail)
  · exact tail

end Leanux.Proofs.Framing
