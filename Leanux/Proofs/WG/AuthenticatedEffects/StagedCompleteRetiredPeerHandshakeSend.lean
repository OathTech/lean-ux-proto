import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeEndpoint

/-! The original response sender preserves exact holder accounting through
its native creation, session, timer and socket outcomes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem create_response (pid : PeerId) : Preserves (Account holders cs loans) (createResponse pid) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_frame) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_view) pid)

theorem mac (pid : PeerId) (msg : List UInt8) : Preserves (Account holders cs loans) (addMacToPacket pid msg) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.addMacToPacket_frame) pid msg)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.addMacToPacket_view) pid msg)

theorem send (pid : PeerId) (msg : List UInt8) : Preserves (Account holders cs loans) (sendBufferToPeer pid msg) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.sendBufferToPeer_frame) pid msg)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendBufferToPeer_view) pid msg)

private theorem last_sent (pid : PeerId) (now : Int64) : Preserves (Input cs loans)
    (getPeer pid >>= fun p => setPeer pid {p with lastSentHandshake:=now}) := by
  apply join
  · exact boundary (fun _ => Account.update
      pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.update) pid _ (fun _ => rfl)
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid _ (fun _ => rfl)

private theorem input_session (pid : PeerId) : Hoare (beginSession pid) (Input cs loans)
    (fun _ => ExactBoundary cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨h,account⟩ := hi.1
  have facts := HandshakeEntry.entry_facts hi.2
  exact ⟨h,session account pid facts.1 facts.2.1 facts.2.2 a b run⟩

private theorem sent (pid : PeerId) : Preserves (Account holders cs loans) (timersAnyAuthenticatedPacketSent pid) :=
  del_timer pid .sendKeepalive

private theorem suffix (pid : PeerId) (msg : List UInt8) : Preserves (Account holders cs loans) (do
    timersSessionDerived pid
    timersTraversal pid
    timersAnyAuthenticatedPacketSent pid
    let now ← hiddenClock64 .respLastSentAgain
    setPeer pid {(←getPeer pid) with lastSentHandshake:=now}
    sendBufferToPeer pid msg) := by
  apply preserves_bind (derived pid)
  intro _
  apply preserves_bind (traversal pid)
  intro _
  apply preserves_bind (sent pid)
  intro _
  apply preserves_bind (show Preserves (Account holders cs loans) (hiddenClock64 .respLastSentAgain : WG.M Int64) from
    hoare_liftAmbient (AmbientM.hiddenClock64 .respLastSentAgain) (Account holders cs loans))
  intro now
  rw [←bind_assoc]
  apply preserves_bind (Account.update
    pid (fun p => {p with lastSentHandshake:=now}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
  intro _
  exact send pid msg

theorem send_response (pid : PeerId) : Hoare (sendHandshakeResponse pid) (Input cs loans)
    (fun _ => ExactBoundary cs loans) := by
  unfold sendHandshakeResponse
  apply hoare_bind _ _ (show Preserves (Input cs loans) (hiddenClock64 .respLastSent : WG.M Int64) from
    hoare_liftAmbient (AmbientM.hiddenClock64 .respLastSent) (Input cs loans))
  intro now
  rw [←bind_assoc]
  apply hoare_bind _ _ (last_sent pid now)
  intro _
  apply hoare_bind _ _ (join _ (boundary (fun _ => create_response pid)) (HandshakeSendResponse.create_entry pid))
  intro created
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .respCreated created.isSome) (Input cs loans))
  intro ready
  cases ready with
  | false => exact hoare_consequence (preserves_pure ()) (fun _ hi => hi.1) (fun _ _ hi => hi)
  | true =>
    cases created with
    | none =>
      exact hoare_consequence (hoare_liftAmbient (AmbientM.invariant "unreachable") (ExactBoundary cs loans))
        (fun _ hi => hi.1) (fun _ _ hi => hi)
    | some msg =>
      apply hoare_bind _ _ (join _ (boundary (fun _ => mac pid msg)) (HandshakeSendResponse.mac_entry pid msg))
      intro bytes
      apply hoare_bind _ _ (input_session pid)
      intro begun
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .respSessionBegun begun) (ExactBoundary cs loans))
      intro active
      cases active with
      | false => exact preserves_pure ()
      | true => exact boundary (fun _ => suffix pid bytes)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
