import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSessionCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendWorkerFrames

/-! Configuration metadata and delayed worker writes expose their original
reads, native decisions and writes. List witnesses follow the actual loop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def listShape (xs : List ι) (initial : σ) (body : ι → σ → WG.M (ForInStep σ))
    (shapes : ∀value acc,Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun values=>∀acc,Shape (forIn values acc body))
    (fun acc=>.access (.pure acc))
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.access (.pure final)
        | .yield next=>ih next)) xs initial

def precomputeCheck (pid : PeerId) (identity : StaticIdentity) : WG.M Bool := do
  let p ← getPeer pid
  if ← branch .precomputeNoIdentity !identity.hasIdentity then pure true
  else
    let (out,nonNull):=curve25519 identity.staticPrivate p.remoteStatic
    setPeer pid {p with precomputedStaticStatic:=out}
    branch .precomputeNullPoint !nonNull

theorem precompute_source (pid : PeerId) : precomputeStaticStatic pid=(do
    requireNotPending pid "recomputing the static-static key"
    let identity:=(←getDev).staticIdentity
    let zero ← precomputeCheck pid identity
    if zero then setPeer pid {(←getPeer pid) with precomputedStaticStatic:=List.replicate 32 0}) := by
  simp only [precomputeStaticStatic,precomputeCheck,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only
    | simp (config := {failIfUnchanged := true}) only [pure_bind,bind_assoc]

noncomputable def precomputeShape (pid : PeerId) : Shape (precomputeStaticStatic pid) := by
  rw [precompute_source]
  unfold requireNotPending
  repeat' first
    | (metadata_source_head precomputeCheck
       unfold precomputeCheck
       apply Shape.saved
       intro p
       repeat' saved_peer_source_step)
    | metadata_source_step

noncomputable def beforeWorkerShape (pid : PeerId) : Shape (SendWorkerFrames.beforeWorker pid) := by
  unfold SendWorkerFrames.beforeWorker
  apply Shape.saved
  intro p
  repeat' saved_peer_source_step

noncomputable def staticIdentityShape (key : Key) : Shape (setStaticIdentityPrivateKey key) := by
  unfold setStaticIdentityPrivateKey requireNotPending
  repeat' first
    | (metadata_source_head ForIn.forIn; apply listShape)
    | metadata_source_step

noncomputable def deviceCookieShape : Shape cookiePrecomputeDeviceKeys := by
  unfold cookiePrecomputeDeviceKeys
  repeat' metadata_source_step

noncomputable def resetHandshakeShape (pid : PeerId) : Shape (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  repeat' metadata_source_step

noncomputable def expireShape (pid : PeerId) : Shape (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairs requireNotPending handshakeClear setKeypair
  repeat' first
    | (metadata_source_head handshakeZero; exact zeroShape _)
    | (metadata_source_head resetLastSentHandshake; exact resetHandshakeShape _)
    | metadata_source_step

noncomputable def clearEndpointShape (pid : PeerId) : Shape (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  repeat' metadata_source_step

noncomputable def setEndpointShape (pid : PeerId) (endpoint : Endpoint) : Shape (setPeerEndpoint pid endpoint) := by
  unfold setPeerEndpoint endpointEq dstCacheReset requireNotPending
  repeat' metadata_source_step

noncomputable def socketReinitShape (sock4 sock6 : Option Nat) : Shape (socketReinit sock4 sock6) := by
  unfold socketReinit sockFree
  repeat' metadata_source_step

noncomputable def socketInitShape (port : Nat) : Shape (socketInit port) := by
  unfold socketInit
  repeat' first
    | (metadata_source_head socketReinit; exact socketReinitShape _ _)
    | metadata_source_step

noncomputable def setPortShape (port : Nat) : Shape (setPort port) := by
  unfold setPort
  repeat' first
    | (metadata_source_head socketInit; exact socketInitShape _)
    | (metadata_source_head clearPeerEndpointSrc; exact clearEndpointShape _)
    | (metadata_source_head ForIn.forIn; apply listShape)
    | metadata_source_step

noncomputable def interfaceShape (ref : DeviceRef) : Shape (lookupInterface ref) := by
  unfold lookupInterface
  repeat' metadata_source_step

noncomputable def peerGetShape (pid : PeerId) : Shape (peerGet pid) := by
  unfold peerGet requireNotPending
  simp only [pure_bind]
  apply Shape.saved
  intro p
  repeat' saved_peer_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
