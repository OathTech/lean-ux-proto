import Leanux.Proofs.WG.HandshakeSecurity.ExchangeControl

/-! Native lifecycle leaves preserve the exchange projection. Whole shutdown
and destruction cannot use these frames in place of their observed drains. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem socket_frame (h : List Event) (action : WG.M α) (same : SameSocket action) :
    Framing.Preserves (StateInv h) action := by
  apply frame_tag h action
  apply same.of_factor
    (fun s : WGOwnedView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.handshakeState)
    handshakeTagAt
  intro w
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]
  rfl

theorem purge_frame (pid : PeerId) (h : List Event) :
    Framing.Preserves (StateInv h) (purgeStagedPackets pid) := by
  apply frame h _
  intro w v a b result run
  unfold purgeStagedPackets at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,tail⟩ := run
  obtain ⟨worldEq,ambientEq,d,hd,hp⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨u,modified,c,changeWorld,setter⟩ := tail
  cases changeWorld
  cases setter
  intro target tag found _
  by_cases eq : pid = target
  · subst target
    simpa [handshakeTagAt,hd,hp] using found
  · simpa [handshakeTagAt,hd,Std.TreeMap.getElem?_insert,eq] using found

theorem reset_sent_frame (pid : PeerId) (h : List Event) :
    Framing.Preserves (StateInv h) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) _)
  intro now
  exact update_peer pid (fun p => {p with lastSentHandshake :=
    now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64}) (fun _ => Or.inl rfl) h

abbrev destructFinishSource : WG.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish

theorem destruct_finish_frame (h : List Event) :
    Framing.Preserves (StateInv h) destructFinishSource := by
  apply frame h _
  intro w v a b result run
  cases result
  have gone := (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish_none)
    w v a b run
  have absent : v.dev = none := by
    simpa only [AllowedIps.routingView,Option.map_eq_none_iff] using gone
  intro pid tag found _
  simp [handshakeTagAt,absent] at found

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
