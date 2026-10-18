import Leanux.Proofs.WG.Roaming.RemoteSessionEffects
import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.Noise.CookieReplyTagFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem remotes_frame_of_sendWork {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option TimerDiscipline.SendWorkDevice)
        (v : Option TimerDiscipline.SendWorkPeer),
      ⦃fun g => ⌜TimerDiscipline.sendWorkAt g pid = (q,v)⌝⦄ action
        ⦃⇓? _ g => ⌜TimerDiscipline.sendWorkAt g pid = (q,v)⌝⦄) :
    SameView destinationAt action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have same := (ensures_iff _ _ _).mpr
    (frame (TimerDiscipline.sendWorkAt g pid).1 (TimerDiscipline.sendWorkAt g pid).2)
    g ambient result final after rfl run
  have projected := congrArg (fun x : TimerDiscipline.SendWorkView =>
    fun target => x.1.bind fun d => (d.2.2 target).bind fun c => c.2.2.2.2.2.2.2.2) same
  funext target
  have point := congrFun projected target
  simpa [destinationAt,peerAt,TimerDiscipline.sendWorkAt,TimerDiscipline.sendWorkKernel,
    TimerDiscipline.sendWorkDevice,TimerDiscipline.sendWorkCell,Option.bind_map,
    Function.comp_def,Option.map_bind,Option.bind_assoc] using point

theorem sendBufferToPeer_spec_remotes_variant (pid : PeerId) (msg : List UInt8) :
    SameView destinationAt (sendBufferToPeer pid msg) :=
  remotes_frame_of_sendWork _ pid
    (TimerDiscipline.sendBufferToPeer_spec_sendWork_variant pid msg)

theorem sendBufferAsReplyToSkb_spec_remotes_variant (src : SkbSource) (msg : List UInt8) :
    SameView destinationAt (sendBufferAsReplyToSkb src msg) :=
  remotes_frame_of_sendWork _ 0 (Noise.sendBufferAsReplyToSkb_sendWorkView 0 src msg)

theorem sameCookie_remotes {α : Type} (action : WG.M α)
    (frame : SameCookie action) : SameView destinationAt action := by
  apply frame.of_factor (fun v : WGOwnedView => fun pid =>
    ((v.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination) destinationAt
  intro g
  funext pid
  cases device : g.dev <;>
    simp [destinationAt,peerAt,cookieView,cookieDevice,wgOwnedView,wgStoreView,device]

theorem sendHandshakeCookie_remotes (msg : List UInt8) (src : SkbSource) :
    SameView destinationAt (sendHandshakeCookie msg src) :=
  (sameCookie_remotes _ (cookieMessageCreate_sameCookie _ _ _)).bind
    (fun buffer => sendBufferAsReplyToSkb_spec_remotes_variant src buffer)

theorem stagingFrame_remotes {entry final : WGWorld} (frame : Index.StagingRich.Frame entry final) :
    RemoteRetained (destinationAt entry) (destinationAt final) := by
  have project (g : WGWorld) (pid : PeerId) :
      destinationAt g pid = (Index.StagingRich.peerMap g pid).bind
        (fun c => c.2.2.2.2.2.2.2) := by
    cases device : g.dev with
    | none => simp [destinationAt,peerAt,Index.StagingRich.peerMap,device]
    | some d =>
      cases resident : d.peers[pid]? with
      | none => simp [destinationAt,peerAt,Index.StagingRich.peerMap,device,resident]
      | some p => simp [destinationAt,peerAt,Index.StagingRich.peerMap,device,resident,
          Index.StagingRich.PeerCell]
  intro pid remote present
  rw [project] at present ⊢
  cases stored : Index.StagingRich.peerMap final pid with
  | none => simp [stored] at present
  | some cell =>
    rw [frame.peers pid cell stored]
    simpa only [stored] using present

theorem staging_remotes {α : Type} (action : WG.M α)
    (frame : ∀ g, Ensures action (Index.StagingRich.Frame g)
      (fun _ => Index.StagingRich.Frame g)) (entry : RemoteMap) :
    Ensures action (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) := by
  intro g ambient result final after pre run
  exact pre.trans (stagingFrame_remotes (frame g g ambient result final after
    (Index.StagingRich.refl g) run))

theorem sendKeepalive_remotes (pid : PeerId) (entry : RemoteMap) :
    Ensures (sendKeepalive pid) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) :=
  staging_remotes _ (Index.StagingRich.sendKeepalive_rich pid) entry

theorem sendStagedPackets_remotes (pid : PeerId) (entry : RemoteMap) :
    Ensures (sendStagedPackets pid) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) :=
  staging_remotes _ (Index.StagingRich.sendStagedPackets_rich pid) entry

theorem sendQueuedHandshakeInitiation_remotes (pid : PeerId) (retry : Bool) (entry : RemoteMap) :
    Ensures (sendQueuedHandshakeInitiation pid retry) (fun g => RemoteRetained entry (destinationAt g))
      (fun _ g => RemoteRetained entry (destinationAt g)) :=
  staging_remotes _ (fun g => (ensures_iff _ _ _).mpr
    (Index.StagingRich.sendQueuedHandshakeInitiation_rich pid retry g)) entry

end Leanux.Proofs.WG.Roaming
