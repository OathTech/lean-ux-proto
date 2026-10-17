import Leanux.Proofs.WG.Config.MultiPeerCoalesceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Exact message-step factor of the original coalescer. -/
def coalesceMessageStep (m : NlMessage)
    (state : Option (List (String × Json)) × Array PeerDumpAttrs × Option Int) :
    WG.M (ForInStep (Option (List (String × Json)) × Array PeerDumpAttrs × Option Int)) := do
  let mut device := state.1
  let peers := state.2.1
  let doneErr := state.2.2
  match m with
  | .error _ =>
    invariant "op 9: an acknowledgement among the dump's chunks"
    return .yield (device,peers,doneErr)
  | .done flags e =>
    if flags != 2 then invariant "op 9: NLMSG_DONE with the consistency flag"
    return .yield (device,peers,some e)
  | .data flags part ps =>
    if flags != 2 then invariant "op 9: NLM_F_DUMP_INTR within one operation"
    if !part.isEmpty then
      match device with
      | none => device := some part
      | some first =>
        if (Json.mkObj first).compress != (Json.mkObj part).compress then
          invariant "op 9: a repeated device part differs"
    let some ps := ps | return .yield (device,peers,doneErr)
    let out ← forIn ps (peers,true) coalescePeerStep
    return .yield (device,out.1,doneErr)

/-- Exact final DONE/error/device checks of the original coalescer. -/
def coalesceFinish (state : Option (List (String × Json)) × Array PeerDumpAttrs × Option Int) :
    WG.M (Except Int Json) := do
  let some e := state.2.2 | invariant "op 9: the dump ended without NLMSG_DONE"
  if e != 0 then return .error e
  let some part := state.1 | invariant "op 9: no device part"
  return .ok (Json.mkObj (part ++ [("peers",Json.arr (state.2.1.map fun p => Json.mkObj p.attrs))]))

/-- Unconditional source factor, retaining every original message error and
its order, including a standalone acknowledgement. -/
theorem coalesce_messages_source (ms : List NlMessage) :
    coalesce ms = (do
      if let [.error e] := ms then return .error e
      let state ← forIn ms (none,#[],none) coalesceMessageStep
      coalesceFinish state) := by
  unfold coalesce coalesceFinish
  congr 1

end Leanux.Proofs.WG.Config
