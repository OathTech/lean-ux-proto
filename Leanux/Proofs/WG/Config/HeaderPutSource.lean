import Leanux.Proofs.WG.Config.HeaderCutSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

def cursorHeaderPut (site : Decision) (cost : Nat) (message : String) (skb : NlSkb) : AmbientM NlSkb := do
  let (fail,out) := skb.put cost
  if ← branch site fail then unsupported message
  return out

def cursorHeaderDevice (d : Device) (skb : NlSkb) : AmbientM (List (String × Json) × NlSkb) := do
  let message := "the device part does not fit a fresh chunk (unreachable)"
  let skb ← cursorHeaderPut .dumpPutPort (nlaTotal 2) message skb
  let skb ← cursorHeaderPut .dumpPutFwmark (nlaTotal 4) message skb
  let skb ← cursorHeaderPut .dumpPutIfindex (nlaTotal 4) message skb
  let skb ← cursorHeaderPut .dumpPutIfname (nlaTotal (d.ifname.length+1)) message skb
  let attrs := [("listen_port",toJson d.incomingPort),("fwmark",toJson d.fwmark),
    ("ifindex",toJson d.ifindex),("ifname",toJson d.ifname)]
  if ← branch .dumpHasIdentity d.staticIdentity.hasIdentity then
    let skb ← cursorHeaderPut .dumpPutPrivate (nlaTotal 32) message skb
    let skb ← cursorHeaderPut .dumpPutPublic (nlaTotal 32) message skb
    return (attrs ++ [("private_key",toJson (hexKey d.staticIdentity.staticPrivate)),
      ("public_key",toJson (hexKey d.staticIdentity.staticPublic))],skb)
  return (attrs,skb)

def cursorHeaderFactored (d : Device) (ctx : DumpCtx) (prev : Nat) (skb : NlSkb) :
    AmbientM (Nat × List (String × Json) × NlSkb) := do
  let skb ← cursorHeaderPut .dumpNoHdr (nlmsgTotal 4)
    "a dump chunk without room for its header (unreachable: every chunk is fresh)" skb
  let flags := 2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0
  if ← branch .dumpFirst ctx.nextPeer.isNone then
    let (attrs,skb) ← cursorHeaderDevice d skb
    return (flags,attrs,skb)
  return (flags,[],skb)

theorem cursorHeaderPrefix_factored (d : Device) (ctx : DumpCtx) (prev : Nat) (skb : NlSkb) :
    cursorHeaderPrefix d ctx prev skb = cursorHeaderFactored d ctx prev skb := by
  have stopBind {α β : Type} (message : String) (next : α → AmbientM β) :
      (AmbientM.unsupported message >>= next) = (AmbientM.unsupported message : AmbientM β) := rfl
  have chooseBind {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : AmbientM α) (next : α → AmbientM β) :
      ((if condition then yes else no) >>= next) =
        (if condition then yes >>= next else no >>= next) := by
    split <;> rfl
  have selfLift {α : Type} (action : AmbientM α) : (monadLift action : AmbientM α) = action := rfl
  simp only [cursorHeaderPrefix,cursorHeaderFactored,cursorHeaderDevice,cursorHeaderPut,
    branch,unsupported,selfLift,bind_assoc,pure_bind,stopBind,chooseBind]

/-- Only normal execution selects the successful put continuation. -/
theorem cursorHeaderPut_continue {α : Type} (site : Decision) (cost : Nat)
    (message : String) (skb : NlSkb) (next : NlSkb → AmbientM α) (Q : α → Ambient → Prop)
    (tail : Noise.Product.Ensures (next (skb.put cost).2) (fun _ => True) Q) :
    Noise.Product.Ensures (do let out ← cursorHeaderPut site cost message skb; next out)
      (fun _ => True) Q := by
  intro ambient value after _ run
  by_cases failed : (skb.put cost).1 = true
  · simp [cursorHeaderPut,branch,AmbientM.branch,failed,unsupported,AmbientM.unsupported] at run
    cases run
  · simp [cursorHeaderPut,branch,AmbientM.branch,failed] at run
    exact tail _ value after trivial run

/-- The recorded decision returns its actual supplied Boolean. -/
theorem cursorHeaderBranch_continue {α : Type} (site : Decision) (outcome : Bool)
    (next : Bool → AmbientM α) (Q : α → Ambient → Prop)
    (tail : Noise.Product.Ensures (next outcome) (fun _ => True) Q) :
    Noise.Product.Ensures (do let value ← branch site outcome; next value) (fun _ => True) Q := by
  intro ambient value after _ run
  change (next outcome).run {ambient with steps := ambient.steps.push {
    decision := site,outcome,netRx := ambient.netRxSection}} = _ at run
  exact tail _ value after trivial run

end Leanux.Proofs.WG.Config
