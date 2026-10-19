import Leanux.Proofs.WG.Progress.PeerInitializationFiniteSource
import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.Proofs.WG.Peers.ConfiguredIdentity

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PeerFinite
open Leanux Leanux.WG

/-- The existing base-creation tail with its initialization callback exposed. -/
def finishWith (init : PeerId → Option Key → WG.M Unit)
    (pid : PeerId) (key : Key) (psk : Option Key) : WG.M Unit := do
  dstCacheReset pid
  init pid psk
  resetLastSentHandshake pid
  ConfiguredIdentity.publishRow pid key

/-- The existing creation factor with just allocation and initializer-tail
callbacks exposed. Maximum-peer refusal still precedes allocation. -/
def createWith (allocate : WG.M Bool)
    (finish : PeerId → Key → Option Key → WG.M Unit)
    (key : Key) (psk : Option Key) : WG.M (Except Int PeerId) := do
  let d ← getDev
  if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
    return .error (-ENOMEM)
  if ← branch .peerCreateNoMem !(← allocate) then return .error (-ENOMEM)
  if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
  Peers.peerCreateCore d.nextPeer key
  finish d.nextPeer key psk
  pure (.ok d.nextPeer)

/-- Full creation with finite allocation and finite guarded precomputation.
Core cursor/stamp writes, cache reset, timestamp and publication are original. -/
def create (key : Key) (psk : Option Key) : WG.M (Except Int PeerId) :=
  createWith (monadLift (hiddenAllocFinite .kmemCacheZallocPeer))
    (finishWith handshakeInit) key psk

theorem createWith_native (key : Key) (psk : Option Key) :
    WG.peerCreate key psk =
      createWith (hiddenAlloc .kmemCacheZallocPeer) (finishWith WG.handshakeInit) key psk := by
  rw [← Peers.peerCreateFactored_eq]
  simp only [Peers.peerCreateFactored,createWith,finishWith,ConfiguredIdentity.publishRow,bind_assoc]

theorem create_source (key : Key) (psk : Option Key) :
    WG.peerCreate key psk = create key psk := by
  have alloc : (hiddenAlloc .kmemCacheZallocPeer : WG.M Bool) =
      monadLift (hiddenAllocFinite .kmemCacheZallocPeer) := by
    change monadLift (AmbientM.hiddenAlloc .kmemCacheZallocPeer) = _
    rw [hiddenAlloc_finite_source]
  have init : WG.handshakeInit = handshakeInit := by
    funext pid psk
    exact handshakeInit_source pid psk
  rw [createWith_native, alloc, init]
  rfl

end Leanux.Proofs.WG.Progress.PeerFinite
