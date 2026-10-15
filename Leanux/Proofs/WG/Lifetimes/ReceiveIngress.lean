import Leanux.Proofs.WG.Lifetimes.ReceiveWorker
import Leanux.Proofs.Framing.WGReceiveHeaders

/-! The original UDP/WireGuard entry, including header rejection, handshake
queue admission and transport consumption. Header/DS-field leaves inspect
bytes only. Queue bookkeeping carries no resident-object access; transport
uses the complete existing consumeData observer, including ENOSPC cleanup. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def appendHandshakeQueue (msg : List UInt8) (src : SkbSource) (d : Device) : Device :=
  {d with handshakeQueue := d.handshakeQueue.produce (msg, src), handshakeQueueLen := d.handshakeQueueLen + 1}

def setHandshakeCpu (cpu : Int) (d : Device) : Device := {d with handshakeLastCpu := cpu}

structure ReceiveIngressContracts (I : List LifetimeEvent → World → Prop) : Prop where
  append : ∀ msg src, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (appendHandshakeQueue msg src)))
  cpu : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (setHandshakeCpu cpu)))
  consume : ∀ msg src ds, PrefixPreserves I LifetimeEvent.Safe (consumeDataPrefix msg src ds)

theorem allocationReceiveIngress : ReceiveIngressContracts AllocationInv := by
  refine ⟨?_, ?_, consumeDataPrefix_allocation⟩
  · intro msg src
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [appendHandshakeQueue, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, appendHandshakeQueue,
        Option.map_map, Function.comp_def] <;> rfl
  · intro cpu
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [setHandshakeCpu, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, setHandshakeCpu,
        Option.map_map, Function.comp_def] <;> rfl

def cpumaskNextOnlinePrefix : MixedM Unit := do
  let next := (← liftPrefix getDev).handshakeLastCpu + 1
  let cpu ← do
    if ← liftPrefix (branch .cpumaskWrap (next ≥ 1)) then pure (0 : Int) else pure next
  liftPrefix (modifyDev (setHandshakeCpu cpu))

def packetReceivePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftPrefix (branch .rxPrepareFailed !(← liftPrefix (prepareSkbHeader msg))) then return
  let t := messageType msg
  if ← liftPrefix (branch .rxHandshake (t == MESSAGE_HANDSHAKE_INITIATION || t == MESSAGE_HANDSHAKE_RESPONSE
                            || t == MESSAGE_HANDSHAKE_COOKIE)) then
    if ← liftPrefix (branch .rxRngNotReady false) then liftPrefix (unsupported "unreachable")
    _ ← liftPrefix (branch .rxQueueBusy ((← liftPrefix getDev).handshakeQueueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2))
    if ← liftPrefix (branch .rxProduceFailed (← liftPrefix getDev).handshakeQueue.full) then return
    liftPrefix (modifyDev (appendHandshakeQueue msg src))
    cpumaskNextOnlinePrefix
    liftPrefix (queueDeviceWork .receiveWorker)
    return
  if ← liftPrefix (branch .rxData (t == MESSAGE_DATA)) then
    let ds ← liftPrefix (ipTunnelGetDsfield (if src.family == 4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src))
    consumeDataPrefix msg src ds
    return
  liftPrefix (invariant "validate_header_len admitted an unknown type")

def wgReceivePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftPrefix (branch .rxNoSock false) then liftPrefix (unsupported "unreachable")
  if ← liftPrefix (branch .rxNoWg false) then liftPrefix (unsupported "unreachable")
  packetReceivePrefix msg src

theorem cpumaskNextOnlinePrefix_erases : ErasesPrefix cpumaskNextOnlinePrefix cpumaskNextOnline := by
  unfold cpumaskNextOnlinePrefix cpumaskNextOnline
  repeat' first
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | (intro x; try dsimp only)
    | split

theorem packetReceivePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (packetReceivePrefix msg src) (packetReceive msg src) := by
  unfold packetReceivePrefix packetReceive
  repeat' first
    | with_reducible exact cpumaskNextOnlinePrefix_erases
    | with_reducible exact consumeDataPrefix_erases _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals exact erasesPrefix_lift _

theorem wgReceivePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (wgReceivePrefix msg src) (wgReceive msg src) := by
  unfold wgReceivePrefix wgReceive
  repeat' first
    | with_reducible exact packetReceivePrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem cpumaskNextOnlinePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I) :
    PrefixPreserves I LifetimeEvent.Safe cpumaskNextOnlinePrefix := by
  unfold cpumaskNextOnlinePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact r.cpu _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem packetReceivePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (packetReceivePrefix msg src) := by
  have hu (why : String) : PrefixPreserves I LifetimeEvent.Safe (liftPrefix (unsupported why) : MixedM Unit) := by
    apply AmbientContracts.drop (c.kernel (fun _ => True) _ _)
    intro w x v hr
    cases hr
  unfold packetReceivePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (prepareSkbHeader_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (ipTunnelGetDsfield_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (queueDeviceWork_sameKernel _))
    | with_reducible exact hu _
    | with_reducible exact r.append _ _
    | with_reducible exact cpumaskNextOnlinePrefix_preserves c r
    | with_reducible exact r.consume _ _ _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem wgReceivePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (wgReceivePrefix msg src) := by
  have hu (why : String) : PrefixPreserves I LifetimeEvent.Safe (liftPrefix (unsupported why) : MixedM Unit) := by
    apply AmbientContracts.drop (c.kernel (fun _ => True) _ _)
    intro w x v hr
    cases hr
  unfold wgReceivePrefix
  repeat' first
    | with_reducible exact hu _
    | with_reducible exact packetReceivePrefix_preserves c r _ _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

inductive ReceiveIngressCall where
  | cpu
  | packet (msg : List UInt8) (src : SkbSource)
  | udp (msg : List UInt8) (src : SkbSource)

namespace ReceiveIngressCall

def original : ReceiveIngressCall → M Unit
  | .cpu => cpumaskNextOnline
  | .packet msg src => packetReceive msg src
  | .udp msg src => wgReceive msg src

def observed : ReceiveIngressCall → MixedM Unit
  | .cpu => cpumaskNextOnlinePrefix
  | .packet msg src => packetReceivePrefix msg src
  | .udp msg src => wgReceivePrefix msg src

theorem erases (call : ReceiveIngressCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | cpu => exact cpumaskNextOnlinePrefix_erases
  | packet msg src => exact packetReceivePrefix_erases msg src
  | udp msg src => exact wgReceivePrefix_erases msg src

theorem preserves_ambient (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (call : ReceiveIngressCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | cpu => exact cpumaskNextOnlinePrefix_preserves c r
  | packet msg src => exact packetReceivePrefix_preserves c r msg src
  | udp msg src => exact wgReceivePrefix_preserves c r msg src

theorem allocation (call : ReceiveIngressCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationReceiveIngress

end ReceiveIngressCall
end Leanux.Proofs.WG.Lifetimes
