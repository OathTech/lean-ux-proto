import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPeerFocus
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! The nested TX repayment records its counted cut while retaining every
existing lifetime access. Matching uses the same actual incoming journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AuthenticatedEffects

def peerEncode (encode : TxDisposition.Event → E) : Peers.PeerEvent → E :=
  encode ∘ TxDisposition.Event.access ∘ LifetimeEvent.peer

def peerDecode (decode : E → Option TxDisposition.Event) (event : E) : Option Peers.PeerEvent :=
  ((decode event).bind TxDisposition.accessEvent).bind LifetimeEvent.peer?

def releaseObserved (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (record : Event → E) (peer : Option PeerId) : PrefixM E Unit :=
  liftWGObserver (PeerSource.observed
    (PeerSource.Ops.focus (peerEncode encode) (peerDecode decode) PeerSource.peers) record peer)

theorem release_target (encode : TxDisposition.Event → E) (decode : E → Option TxDisposition.Event)
    (peer : Option PeerId) :
    liftWGObserver (focusStatePrefix (peerEncode encode) (peerDecode decode) (Peers.peerPutPrefix peer)) =
      focusPrefix encode decode (native.release peer) := by
  simp only [native,TxDisposition.nativeAccess,TxDisposition.access,peerPutMixed,peerStateFocus,
    CompletionEffects.lift_focus,CompletionEffects.focus_composed]
  unfold peerEncode peerDecode
  simp only [Option.bind_assoc]

theorem release_matching (ρ : E → Option F)
    (eg : TxDisposition.Event → E) (dg : E → Option TxDisposition.Event)
    (et : TxDisposition.Event → F) (dt : F → Option TxDisposition.Event)
    (enc : ∀ event, ρ (eg event) = some (et event))
    (dec : ∀ event, dg event = (ρ event).bind dt)
    (inverse : ∀ event, dt (et event) = some event)
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    ProjectsPrefix ρ id (releaseObserved eg dg record peer)
      (focusPrefix et dt (native.release peer)) := by
  have encode : ∀ event, ρ (peerEncode eg event) = some (peerEncode et event) :=
    fun event => enc (.access (.peer event))
  have decode : ∀ event, peerDecode dg event = (ρ event).bind (peerDecode dt) := by
    intro event
    change ((dg event).bind TxDisposition.accessEvent).bind LifetimeEvent.peer? =
      (ρ event).bind (fun value => ((dt value).bind TxDisposition.accessEvent).bind LifetimeEvent.peer?)
    rw [dec]
    simp only [Option.bind_assoc]
  have project : PeerSource.Ops.Projects ρ
      (PeerSource.Ops.focus (peerEncode eg) (peerDecode dg) PeerSource.peers)
      (PeerSource.Ops.focus (peerEncode et) (peerDecode dt) PeerSource.peers) := by
    constructor
    all_goals intros
    all_goals exact CompletionEffects.state_focus_matching ρ _ _ _ _ encode decode _
  have projected := PeerSource.observed_focused_peers_projects ρ (peerEncode et) (peerDecode dt)
    (fun event => by simp [peerEncode,peerDecode,inverse,TxDisposition.accessEvent,LifetimeEvent.peer?])
    project record quiet peer
  rw [← release_target et dt peer]
  exact projected.liftWGObserver ρ id

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
