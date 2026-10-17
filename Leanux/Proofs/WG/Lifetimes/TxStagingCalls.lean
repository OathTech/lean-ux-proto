import Leanux.Proofs.WG.Lifetimes.TxStaging

/-! The complete TX staging family, with the CPU and enqueue return values
retained. These per-call contracts compose through the existing bind and
finite-loop laws. Workers, socket transmission, ownership, and delivery
guarantees are not conclusions. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive TxStagingCall where
  | cpu (pid : PeerId)
  | peerEnqueue (item : List SkbId) (state : PacketState)
  | deviceEnqueue (pid : PeerId) (item : List SkbId)
  | create (pid : PeerId) (item : List SkbId)
  | purge (pid : PeerId)
  | send (pid : PeerId)
  | keepalive (pid : PeerId)

namespace TxStagingCall

def Result : TxStagingCall → Type
  | .cpu _ => Nat
  | .deviceEnqueue _ _ => Int
  | _ => Unit

def original (call : TxStagingCall) : WG.M call.Result := match call with
  | .cpu pid => cpumaskChooseOnline pid
  | .peerEnqueue item state => enqueuePerPeerTx item state
  | .deviceEnqueue pid item => enqueuePerDeviceAndPeer pid item
  | .create pid item => createData pid item
  | .purge pid => purgeStagedPackets pid
  | .send pid => sendStagedPackets pid
  | .keepalive pid => sendKeepalive pid

def observed (call : TxStagingCall) : MixedM call.Result := match call with
  | .cpu pid => cpumaskChooseOnlinePrefix pid
  | .peerEnqueue item state => enqueuePerPeerTxPrefix item state
  | .deviceEnqueue pid item => enqueuePerDeviceAndPeerPrefix pid item
  | .create pid item => createDataPrefix pid item
  | .purge pid => purgeStagedPacketsPrefix pid
  | .send pid => sendStagedPacketsPrefix pid
  | .keepalive pid => sendKeepalivePrefix pid

theorem erases (call : TxStagingCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | cpu pid => exact cpumaskChooseOnlinePrefix_erases pid
  | peerEnqueue item state => exact enqueuePerPeerTxPrefix_erases item state
  | deviceEnqueue pid item => exact enqueuePerDeviceAndPeerPrefix_erases pid item
  | create pid item => exact createDataPrefix_erases pid item
  | purge pid => exact purgeStagedPacketsPrefix_erases pid
  | send pid => exact sendStagedPacketsPrefix_erases pid
  | keepalive pid => exact sendKeepalivePrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (call : TxStagingCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | cpu pid => exact cpumaskChooseOnlinePrefix_preserves_ambient c pid
  | peerEnqueue item state => exact enqueuePerPeerTxPrefix_preserves_ambient c t item state
  | deviceEnqueue pid item => exact enqueuePerDeviceAndPeerPrefix_preserves_ambient c t pid item
  | create pid item => exact createDataPrefix_preserves_ambient c t pid item
  | purge pid => exact purgeStagedPacketsPrefix_preserves_ambient c t pid
  | send pid => exact sendStagedPacketsPrefix_preserves_ambient c t pid
  | keepalive pid => exact sendKeepalivePrefix_preserves_ambient c t pid

theorem preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (call : TxStagingCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | cpu pid => exact cpumaskChooseOnlinePrefix_preserves_product c pid
  | peerEnqueue item state => exact enqueuePerPeerTxPrefix_preserves_product c t item state
  | deviceEnqueue pid item => exact enqueuePerDeviceAndPeerPrefix_preserves_product c t pid item
  | create pid item => exact createDataPrefix_preserves_product c t pid item
  | purge pid => exact purgeStagedPacketsPrefix_preserves_product c t pid
  | send pid => exact sendStagedPacketsPrefix_preserves_product c t pid
  | keepalive pid => exact sendKeepalivePrefix_preserves_product c t pid

theorem allocation (call : TxStagingCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationTx

end TxStagingCall

/-- An absent/malformed allocation record can fail after the initial peer read.
The premises are original operations, not observer log assumptions. -/
theorem sendKeepalivePrefix_alloc_failure (pid : PeerId) (w checked : WGWorld) (ambient checkedAmbient : Ambient) (p : Peer)
    (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hb : ((branch .keepaliveStagedEmpty p.staged.isEmpty : WG.M Bool).run w).run ambient =
      .ok ((true, checked), checkedAmbient))
    (ha : ((hiddenAlloc .keepaliveSkb : WG.M Bool).run checked).run checkedAmbient = .error e) :
    runStatePrefix (sendKeepalivePrefix pid) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId)]) := by
  simp [sendKeepalivePrefix, runStatePrefix_bind, getPeerMixed_run, hp,
    liftWGPrefix, hb, ha]

end Leanux.Proofs.WG.Lifetimes
