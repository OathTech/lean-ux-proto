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

structure ReceiveIngressContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  append : ∀ msg src, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev (appendHandshakeQueue msg src)))
  cpu : ∀ cpu, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (modifyDev (setHandshakeCpu cpu)))
  consume : ∀ msg src ds, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeDataPrefix msg src ds)

structure ProductReceiveIngressContracts (I : List LifetimeEvent → World → Prop) : Prop where
  append : ∀ msg src, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (modifyDev (appendHandshakeQueue msg src))))
  cpu : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (modifyDev (setHandshakeCpu cpu))))
  consume : ∀ msg src ds, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeDataPrefix msg src ds))

theorem allocationReceiveIngress : ReceiveIngressContracts AllocationInv := by
  refine ⟨?_, ?_, consumeDataPrefix_allocation⟩
  · intro msg src
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [appendHandshakeQueue, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, appendHandshakeQueue,
        Option.map_map, Function.comp_def] <;> rfl
  · intro cpu
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [setHandshakeCpu, Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, setHandshakeCpu,
        Option.map_map, Function.comp_def] <;> rfl

def cpumaskNextOnlinePrefix : MixedM Unit := do
  let next := (← liftWGPrefix getDev).handshakeLastCpu + 1
  let cpu ← do
    if ← liftWGPrefix (branch .cpumaskWrap (next ≥ 1)) then pure (0 : Int) else pure next
  liftWGPrefix (modifyDev (setHandshakeCpu cpu))

def packetReceivePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftWGPrefix (branch .rxPrepareFailed !(← liftWGPrefix (prepareSkbHeader msg))) then return
  let t := messageType msg
  if ← liftWGPrefix (branch .rxHandshake (t == MESSAGE_HANDSHAKE_INITIATION || t == MESSAGE_HANDSHAKE_RESPONSE
                            || t == MESSAGE_HANDSHAKE_COOKIE)) then
    if ← liftWGPrefix (branch .rxRngNotReady false) then liftWGPrefix (unsupported "unreachable")
    _ ← liftWGPrefix (branch .rxQueueBusy ((← liftWGPrefix getDev).handshakeQueueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2))
    if ← liftWGPrefix (branch .rxProduceFailed (← liftWGPrefix getDev).handshakeQueue.full) then return
    liftWGPrefix (modifyDev (appendHandshakeQueue msg src))
    cpumaskNextOnlinePrefix
    liftWGPrefix (queueDeviceWork .receiveWorker)
    return
  if ← liftWGPrefix (branch .rxData (t == MESSAGE_DATA)) then
    let ds ← liftWGPrefix (ipTunnelGetDsfield (if src.family == 4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src))
    consumeDataPrefix msg src ds
    return
  liftWGPrefix (invariant "validate_header_len admitted an unknown type")

def wgReceivePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftWGPrefix (branch .rxNoSock false) then liftWGPrefix (unsupported "unreachable")
  if ← liftWGPrefix (branch .rxNoWg false) then liftWGPrefix (unsupported "unreachable")
  packetReceivePrefix msg src

theorem cpumaskNextOnlinePrefix_erases : ErasesStatePrefix cpumaskNextOnlinePrefix cpumaskNextOnline := by
  unfold cpumaskNextOnlinePrefix cpumaskNextOnline
  repeat' first
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | apply erasesStatePrefix_ite
    | (intro x; try dsimp only)
    | split

theorem packetReceivePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (packetReceivePrefix msg src) (packetReceive msg src) := by
  unfold packetReceivePrefix packetReceive
  repeat' first
    | with_reducible exact cpumaskNextOnlinePrefix_erases
    | with_reducible exact consumeDataPrefix_erases _ _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erasesStatePrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals exact erasesStatePrefix_lift _

theorem wgReceivePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (wgReceivePrefix msg src) (wgReceive msg src) := by
  unfold wgReceivePrefix wgReceive
  repeat' first
    | with_reducible exact packetReceivePrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erasesStatePrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem cpumaskNextOnlinePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (cpumaskNextOnlinePrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold cpumaskNextOnlinePrefix
  repeat' first
    | (maintenance_lift_action_head modifyDev; exact r.cpu _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem packetReceivePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (packetReceivePrefix msg src) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold packetReceivePrefix
  repeat' first
    | (maintenance_lift_action_head prepareSkbHeader; exact AmbientContracts.drop (c.store (fun _ => True) _ ((prepareSkbHeader_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head ipTunnelGetDsfield; exact AmbientContracts.drop (c.store (fun _ => True) _ ((ipTunnelGetDsfield_sameWGWorld _ _).factor wgStoreView)))
    | (maintenance_lift_action_head queueDeviceWork; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.queueDeviceWork _)))
    | (maintenance_lift_action_head modifyDev; exact r.append _ _)
    | (maintenance_head cpumaskNextOnlinePrefix; exact cpumaskNextOnlinePrefix_preserves c r)
    | (maintenance_head consumeDataPrefix; exact r.consume _ _ _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgReceivePrefix_preserves (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (wgReceivePrefix msg src) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgReceivePrefix
  repeat' first
    | (maintenance_head packetReceivePrefix; exact packetReceivePrefix_preserves c r _ _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem cpumaskNextOnlinePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductReceiveIngressContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (cpumaskNextOnlinePrefix)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold cpumaskNextOnlinePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_lift_action_head modifyDev; exact r.cpu _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem packetReceivePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (packetReceivePrefix msg src)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold packetReceivePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_lift_action_head prepareSkbHeader; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((prepareSkbHeader_sameWGWorld _).factor wgStoreView)))
    | (maintenance_lift_action_head ipTunnelGetDsfield; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((ipTunnelGetDsfield_sameWGWorld _ _).factor wgStoreView)))
    | (maintenance_lift_action_head queueDeviceWork; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.queueDeviceWork _)))
    | (maintenance_lift_action_head modifyDev; exact r.append _ _)
    | (maintenance_head cpumaskNextOnlinePrefix; exact cpumaskNextOnlinePrefix_preserves_product c r)
    | (maintenance_head consumeDataPrefix; exact r.consume _ _ _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgReceivePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductReceiveIngressContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgReceivePrefix msg src)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgReceivePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_head packetReceivePrefix; exact packetReceivePrefix_preserves_product c r _ _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

inductive ReceiveIngressCall where
  | cpu
  | packet (msg : List UInt8) (src : SkbSource)
  | udp (msg : List UInt8) (src : SkbSource)

namespace ReceiveIngressCall

def original : ReceiveIngressCall → WG.M Unit
  | .cpu => cpumaskNextOnline
  | .packet msg src => packetReceive msg src
  | .udp msg src => wgReceive msg src

def observed : ReceiveIngressCall → MixedM Unit
  | .cpu => cpumaskNextOnlinePrefix
  | .packet msg src => packetReceivePrefix msg src
  | .udp msg src => wgReceivePrefix msg src

theorem erases (call : ReceiveIngressCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | cpu => exact cpumaskNextOnlinePrefix_erases
  | packet msg src => exact packetReceivePrefix_erases msg src
  | udp msg src => exact wgReceivePrefix_erases msg src

theorem preserves_ambient (c : AmbientContracts I) (r : ReceiveIngressContracts I)
    (call : ReceiveIngressCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | cpu => exact cpumaskNextOnlinePrefix_preserves c r
  | packet msg src => exact packetReceivePrefix_preserves c r msg src
  | udp msg src => exact wgReceivePrefix_preserves c r msg src

theorem preserves_ambient_product (c : ProductAmbientContracts I) (r : ProductReceiveIngressContracts I)
    (call : ReceiveIngressCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | cpu => exact cpumaskNextOnlinePrefix_preserves_product c r
  | packet msg src => exact packetReceivePrefix_preserves_product c r msg src
  | udp msg src => exact wgReceivePrefix_preserves_product c r msg src

theorem allocation (call : ReceiveIngressCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationReceiveIngress

end ReceiveIngressCall
end Leanux.Proofs.WG.Lifetimes
