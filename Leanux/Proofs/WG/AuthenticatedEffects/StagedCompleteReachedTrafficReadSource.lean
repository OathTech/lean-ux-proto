import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadCanonical

/-! Source trees for traffic's read-only fixture helpers. Their branches,
getter points and failure results remain those of the original functions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

noncomputable def trafficConditionalShape (test : Prop) [Decidable test]
    {yes no : Leanux.M α} (left : test → Shape yes) (right : ¬test → Shape no) :
    Shape (if test then yes else no) := by
  split
  · exact left ‹_›
  · exact right ‹_›

macro "traffic_read_step" : tactic => `(tactic| first
  | exact routingShape
  | exact environmentShape
  | exact Shape.ambient AmbientM.pendingDeviceUnits
  | apply trafficConditionalShape
  | product_read_step)

noncomputable def senderShape (family dest tos : Nat) (ll : Bool) :
    Shape (Env.senderSource family dest tos ll) := by
  unfold Env.senderSource
  repeat' traffic_read_step

noncomputable def packetShape (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    Shape (Env.xmitPacket family addr payload mtu tos) := by
  unfold Env.xmitPacket
  repeat' traffic_read_step

noncomputable def packetsShape (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Shape (Env.xmitPackets family addr payload opts) := by
  unfold Env.xmitPackets
  repeat' first | exact packetShape _ _ _ _ _ | traffic_read_step

noncomputable def drainedShape (what : String) (flags : List Bool) :
    Shape (Env.requireDrained what flags) := by
  unfold Env.requireDrained
  repeat' traffic_read_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
