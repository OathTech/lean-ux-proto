import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Lifetimes.TxStaging
import Leanux.Proofs.Framing.WGSocketLifecycle
import Leanux.WG.Device

/-! Complete socket and device control observations. Socket initialization,
reinitialization and freeing inspect only device/socket scalars and records;
their lifts add no resident-object events. Device loops retain saved scalar
peer IDs and resolve actual objects at each original access. Ordinary negative
returns and Stops keep their distinct cleanup behavior. No queue-progress,
reference-credit, valid-list or distinctness premise is imposed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem socketKernel_identity_metadata (w v : World)
    (he : socketKernelView v = socketKernelView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [socketKernelView, socketKernel, socketDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [socketKernelView, socketKernel, socketDevice, Option.map_map, Function.comp_def] using hm

/-- Arbitrary ambient invariants must explicitly permit socket scalar changes. -/
def SocketControlStable (I : List LifetimeEvent → World → Prop) : Prop :=
  ∀ h w v, socketKernelView v = socketKernelView w → I h w → I h v

theorem allocationSocketControlStable : SocketControlStable AllocationInv := by
  intro h w v he hi
  have hf := socketKernel_identity_metadata w v he
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem socketControlLift_preserves (c : AmbientContracts I) (hs : SocketControlStable I)
    (a : M α) (ha : SameSocketKernel a) :
    PrefixPreserves I LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a c.safe
  intro h w x v hi hr
  exact hs h w v (ha w x v hr) hi

def wgOpenPrefix : MixedM Int := do
  let dev ← liftPrefix getDev
  _ ← liftPrefix (branch .openHasInet dev.inet4Dev)
  _ ← liftPrefix (branch .openHasInet6 dev.inet6Dev)
  let d ← liftPrefix getDev
  let ret ← liftPrefix (socketInit d.incomingPort)
  if ← liftPrefix (branch .openSocketError (ret < 0)) then return ret
  for pid in d.peerList do
    _ ← liftPrefix (branch .openPeersIter true)
    sendStagedPacketsPrefix pid
    if ← liftPrefix (branch .openKeepalive ((← getPeerMixed pid).persistentKeepaliveInterval != 0)) then
      sendKeepalivePrefix pid
  _ ← liftPrefix (branch .openPeersIter false)
  return 0

def wgUpPrefix : MixedM Int := do
  liftPrefix (modifyDev fun d => {d with running := true})
  let ret ← wgOpenPrefix
  if ret < 0 then liftPrefix (modifyDev fun d => {d with running := false})
  return ret

def wgStopPrefix : MixedM Unit := do
  for pid in (← liftPrefix getDev).peerList do
    _ ← liftPrefix (branch .stopPeersIter true)
    requireNotPendingMixed pid "wg_stop while a handshake is queued"
    purgeStagedPacketsPrefix pid
    timersStopPrefix pid
    handshakeClearPrefix pid
    keypairsClearPrefix pid
    resetLastSentHandshakePrefix pid
  _ ← liftPrefix (branch .stopPeersIter false)
  if !(← liftPrefix getDev).handshakeQueue.empty then
    liftPrefix (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)")
  _ ← liftPrefix (branch .stopDrainIter false)
  liftPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})
  liftPrefix (socketReinit none none)

def wgDownPrefix : MixedM Unit := do
  liftPrefix (modifyDev fun d => {d with running := false})
  wgStopPrefix

def netnsPreExitPrefix : MixedM Unit := do
  if (← liftPrefix getK).wg.isSome then
    _ ← liftPrefix (branch .preExitDevIter true)
    if ← liftPrefix (branch .preExitCreator (← liftPrefix getDev).creatingNet) then
      liftPrefix (modifyDev fun d => {d with carrier := false, creatingNet := false})
      liftPrefix (socketReinit none none)
      for pid in (← liftPrefix getDev).peerList do
        _ ← liftPrefix (branch .preExitPeerIter true)
        clearPeerEndpointSrcPrefix pid
      _ ← liftPrefix (branch .preExitPeerIter false)
  _ ← liftPrefix (branch .preExitDevIter false)

theorem wgOpenPrefix_erases : ErasesPrefix wgOpenPrefix wgOpen := by
  unfold wgOpenPrefix wgOpen
  repeat' first
    | with_reducible exact sendStagedPacketsPrefix_erases _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgUpPrefix_erases : ErasesPrefix wgUpPrefix wgUp := by
  unfold wgUpPrefix wgUp
  repeat' first
    | with_reducible exact wgOpenPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgStopPrefix_erases : ErasesPrefix wgStopPrefix wgStop := by
  unfold wgStopPrefix wgStop
  repeat' first
    | with_reducible exact requireNotPendingMixed_erases _ _
    | with_reducible exact purgeStagedPacketsPrefix_erases _
    | with_reducible exact timersStopPrefix_erases _
    | with_reducible exact handshakeClearPrefix_erases _
    | with_reducible exact keypairsClearPrefix_erases _
    | with_reducible exact resetLastSentHandshakePrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDownPrefix_erases : ErasesPrefix wgDownPrefix wgDown :=
  erasesPrefix_bind (erasesPrefix_lift _) (fun _ => wgStopPrefix_erases)

theorem netnsPreExitPrefix_erases : ErasesPrefix netnsPreExitPrefix netnsPreExit := by
  unfold netnsPreExitPrefix netnsPreExit
  repeat' first
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

structure DeviceControlContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : SocketControlStable I
  tx : TxContracts I
  removal : PeerRemovalContracts I
  running : ∀ b, PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with running := b}))
  clearHandshakeQueue : PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with handshakeQueueLen := 0}))
  creatorExit : PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with carrier := false, creatingNet := false}))

theorem allocationDeviceControl : DeviceControlContracts AllocationInv := by
  refine ⟨allocationSocketControlStable, allocationTx, allocationPeerRemoval, ?_, ?_, ?_⟩
  all_goals
    try intro b
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    apply hi.congr
    · cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl

theorem wgOpenPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgOpenPrefix := by
  unfold wgOpenPrefix
  repeat' first
    | with_reducible exact sendStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c r.tx _
    | with_reducible exact socketControlLift_preserves c r.socket _ (socketInit_sameSocketKernel _)
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgUpPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgUpPrefix := by
  unfold wgUpPrefix
  repeat' first
    | with_reducible exact wgOpenPrefix_preserves c r
    | with_reducible exact r.running _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgStopPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgStopPrefix := by
  unfold wgStopPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact purgeStagedPacketsPrefix_preserves_ambient c r.tx _
    | with_reducible exact timersStopPrefix_preserves c r.removal _
    | with_reducible exact handshakeClearPrefix_preserves c r.removal.indexRemove _
    | with_reducible exact keypairsClearPrefix_preserves_ambient c r.removal.keypairPut _
    | with_reducible exact AmbientContracts.drop (resetLastSentHandshakePrefix_spec c (fun _ => True) _)
    | with_reducible exact socketControlLift_preserves c r.socket _ (socketReinit_sameSocketKernel _ _)
    | with_reducible exact r.clearHandshakeQueue
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr <;> rfl))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDownPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgDownPrefix :=
  PrefixPreserves.bind (r.running false) (fun _ => wgStopPrefix_preserves c r)

theorem netnsPreExitPrefix_preserves (c : AmbientContracts I) (r : DeviceControlContracts I) :
    PrefixPreserves I LifetimeEvent.Safe netnsPreExitPrefix := by
  unfold netnsPreExitPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact socketControlLift_preserves c r.socket _ (socketReinit_sameSocketKernel _ _)
    | with_reducible exact r.creatorExit
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) getK (by intro w x v hr; cases hr; rfl))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

inductive DeviceControlCall where
  | freeSocket (sock : Option Nat)
  | reinit (new4 new6 : Option Nat)
  | init (port : Nat)
  | openDevice
  | up
  | stopDevice
  | down
  | preExit

namespace DeviceControlCall

def Result : DeviceControlCall → Type
  | .init _ | .openDevice | .up => Int
  | _ => Unit

def original (call : DeviceControlCall) : M call.Result := match call with
  | .freeSocket sock => sockFree sock
  | .reinit new4 new6 => socketReinit new4 new6
  | .init port => socketInit port
  | .openDevice => wgOpen
  | .up => wgUp
  | .stopDevice => wgStop
  | .down => wgDown
  | .preExit => netnsPreExit

def observed (call : DeviceControlCall) : MixedM call.Result := match call with
  | .freeSocket sock => liftPrefix (sockFree sock)
  | .reinit new4 new6 => liftPrefix (socketReinit new4 new6)
  | .init port => liftPrefix (socketInit port)
  | .openDevice => wgOpenPrefix
  | .up => wgUpPrefix
  | .stopDevice => wgStopPrefix
  | .down => wgDownPrefix
  | .preExit => netnsPreExitPrefix

theorem erases (call : DeviceControlCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | freeSocket sock => exact erasesPrefix_lift _
  | reinit new4 new6 => exact erasesPrefix_lift _
  | init port => exact erasesPrefix_lift _
  | openDevice => exact wgOpenPrefix_erases
  | up => exact wgUpPrefix_erases
  | stopDevice => exact wgStopPrefix_erases
  | down => exact wgDownPrefix_erases
  | preExit => exact netnsPreExitPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : DeviceControlContracts I)
    (call : DeviceControlCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | freeSocket sock => exact AmbientContracts.drop (c.kernel (fun _ => True) _ (sockFree_sameKernel sock))
  | reinit new4 new6 => exact socketControlLift_preserves c r.socket _ (socketReinit_sameSocketKernel new4 new6)
  | init port => exact socketControlLift_preserves c r.socket _ (socketInit_sameSocketKernel port)
  | openDevice => exact wgOpenPrefix_preserves c r
  | up => exact wgUpPrefix_preserves c r
  | stopDevice => exact wgStopPrefix_preserves c r
  | down => exact wgDownPrefix_preserves c r
  | preExit => exact netnsPreExitPrefix_preserves c r

theorem allocation (call : DeviceControlCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDeviceControl

end DeviceControlCall
end Leanux.Proofs.WG.Lifetimes
