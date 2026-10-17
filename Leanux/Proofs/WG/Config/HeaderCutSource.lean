import Leanux.Proofs.WG.Config.CursorBodySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Original header-only computation in its actual Ambient monad. -/
def cursorHeaderPrefix (d : Device) (ctx0 : DumpCtx) (prevSeq0 : Nat) (skb0 : NlSkb) :
    AmbientM (Nat × List (String × Json) × NlSkb) := do
  let seq := d.deviceUpdateGen   -- cb->seq (:222)
  let mut ctx := ctx0
  let (fail, skb) := skb0.put (nlmsgTotal 4)   -- genlmsg_put: nlmsghdr + genlmsghdr
  if ← branch .dumpNoHdr fail then unsupported "a dump chunk without room for its header (unreachable: every chunk is fresh)"
  let mut skb := skb
  -- genl_dump_check_consistent (:229): NLM_F_DUMP_INTR iff the device changed
  -- between two dump calls (2.4); NLM_F_MULTI always
  let flags := 2 + (if prevSeq0 != 0 && prevSeq0 != seq then 16 else 0)
  let mut device : List (String × Json) := []
  if ← branch .dumpFirst ctx.nextPeer.isNone then
    let (fail, s) := skb.put (nlaTotal 2); skb := s
    if ← branch .dumpPutPort fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .dumpPutFwmark fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal 4); skb := s
    if ← branch .dumpPutIfindex fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    let (fail, s) := skb.put (nlaTotal (d.ifname.length + 1)); skb := s
    if ← branch .dumpPutIfname fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
    device := [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
      ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)]
    let identity := d.staticIdentity
    if ← branch .dumpHasIdentity identity.hasIdentity then
      let (fail, s) := skb.put (nlaTotal 32); skb := s
      if ← branch .dumpPutPrivate fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
      let (fail, s) := skb.put (nlaTotal 32); skb := s
      if ← branch .dumpPutPublic fail then unsupported "the device part does not fit a fresh chunk (unreachable)"
      device := device ++ [("private_key", toJson (hexKey identity.staticPrivate)),
        ("public_key", toJson (hexKey identity.staticPublic))]
  return (flags,device,skb)

/-- Exact lifting of the original header, for arbitrary continuation and all errors. -/
theorem cursorHeader_source (d : Device) (ctx : DumpCtx) (prev : Nat) (skb : NlSkb)
    (finish : Nat → List (String × Json) → NlSkb → WG.M DumpCall) :
    socketDumpHeaderSource d ctx prev skb finish = (do
      let (flags,attrs,out) ← cursorHeaderPrefix d ctx prev skb
      finish flags attrs out) := by
  have selfLift {α : Type} (action : AmbientM α) : (monadLift action : AmbientM α) = action := rfl
  have stopBind {α β : Type} (message : String) (next : α → WG.M β) :
      ((monadLift (AmbientM.unsupported message) : WG.M α) >>= next) =
        (monadLift (AmbientM.unsupported message) : WG.M β) := rfl
  have stopBindAmbient {α β : Type} (message : String) (next : α → AmbientM β) :
      (AmbientM.unsupported message >>= next) = (AmbientM.unsupported message : AmbientM β) := rfl
  have chooseBind {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by
    split <;> rfl
  simp only [socketDumpHeaderSource,cursorHeaderPrefix,branch,unsupported,selfLift,
    apply_ite,monadLift_bind,monadLift_pure,bind_assoc,pure_bind,stopBind,stopBindAmbient,chooseBind]


end Leanux.Proofs.WG.Config
