import Leanux.Proofs.WG.Queues.HandshakeResponse
import Leanux.Proofs.WG.Queues.HolderConfigUpdate

/-! The real handshake-response sender retains its charged holders. Session
allocation uses the transported entry facts, and socket failure stays partial. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

private theorem create_frame (pid : PeerId) : ∀ initial, Preserves (Frame initial) (createResponse pid) := by
  intro initial
  change Preserves (Frame initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | receive_crypto (Frame initial) | holder_work_step initial

private theorem create_view (pid : PeerId) :
    SameView (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) (createResponse pid) := by
  intro initial
  change Preserves (fun w => (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | receive_crypto (fun w => (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view) w = initial)
    | send_work_step initial

theorem create_boundary (pid : PeerId) : Preserves (Boundary cs loans) (createResponse pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ (create_frame pid) (fun _ _ =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps) (create_view pid))

private theorem create_slots (pid : PeerId) : Preserves CurrentSlots.Inv (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first
    | receive_crypto CurrentSlots.Inv
    | (allocation_release_lift_from IndexM
       apply hoare_liftIndex
       intro w d table hi hd
       simpa only [CurrentSlots.Inv,Affiliation.view,hd,Option.map_some,Affiliation.state] using hi)
    | slot_traffic_step

theorem create_entry (pid : PeerId) : Preserves HandshakeEntry.Entry (createResponse pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.create) pid)
    (create_slots pid)

theorem mac_boundary (pid : PeerId) (msg : List UInt8) :
    Preserves (Boundary cs loans) (addMacToPacket pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.addMacToPacket_frame) pid msg)
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.addMacToPacket_view) pid msg))

private theorem mac_slots (pid : PeerId) (msg : List UInt8) : Preserves CurrentSlots.Inv (addMacToPacket pid msg) := by
  apply CurrentSlots.fields_preserves (project := id)
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => CurrentSlots.fields w = initial))
    | slot_fields_step initial

theorem mac_entry (pid : PeerId) (msg : List UInt8) :
    Preserves HandshakeEntry.Entry (addMacToPacket pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.mac) pid msg)
    (mac_slots pid msg)

theorem send_boundary (pid : PeerId) (msg : List UInt8) :
    Preserves (Boundary cs loans) (sendBufferToPeer pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.sendBufferToPeer_frame) pid msg)
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendBufferToPeer_view) pid msg))

private theorem join (action : WG.M α) (boundary : Preserves (Boundary cs loans) action)
    (entry : Preserves HandshakeEntry.Entry action) : Preserves (Input cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp boundary w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp entry w a x v b hi.2 run⟩

private theorem lastSent (pid : PeerId) (now : Int64) : Preserves (Input cs loans)
    (getPeer pid >>= fun p => setPeer pid {p with lastSentHandshake:=now}) := by
  apply join
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.update)
      pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.update) pid _ (fun _ => rfl)
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid _ (fun _ => rfl)

private theorem session (pid : PeerId) : Hoare (beginSession pid) (Input cs loans)
    (fun _ => Boundary cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨h,funded,stable⟩ := hi.1
  have facts := HandshakeEntry.entry_facts hi.2
  have post := SessionCarrier.beginSession_funded pid funded stable facts.1 facts.2.1 facts.2.2 a b run
  exact ⟨h,post.1,post.2.1⟩

private theorem sent (pid : PeerId) : Preserves (Boundary cs loans) (timersAnyAuthenticatedPacketSent pid) :=
  HolderTimers.delTimer_boundary pid .sendKeepalive

private theorem suffix (pid : PeerId) (msg : List UInt8) : Preserves (Boundary cs loans) (do
    timersSessionDerived pid
    timersTraversal pid
    timersAnyAuthenticatedPacketSent pid
    let now ← hiddenClock64 .respLastSentAgain
    setPeer pid {(←getPeer pid) with lastSentHandshake:=now}
    sendBufferToPeer pid msg) := by
  apply preserves_bind (HandshakeReceive.sessionDerived pid)
  intro _
  apply preserves_bind (HandshakeReceive.traversal pid)
  intro _
  apply preserves_bind (sent pid)
  intro _
  apply preserves_bind (show Preserves (Boundary cs loans) (hiddenClock64 .respLastSentAgain : WG.M Int64) from
    hoare_liftAmbient (AmbientM.hiddenClock64 .respLastSentAgain) (Boundary cs loans))
  intro now
  rw [←bind_assoc]
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.update)
    pid (fun p => {p with lastSentHandshake:=now}) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
  intro _
  exact send_boundary pid msg

/-- Every actual normal response send retains its existing holder account.
The source's real session entry bounds are transported from the input. -/
theorem sendResponse (pid : PeerId) : Hoare (sendHandshakeResponse pid) (Input cs loans)
    (fun _ => Boundary cs loans) := by
  unfold sendHandshakeResponse
  apply hoare_bind _ _ (show Preserves (Input cs loans) (hiddenClock64 .respLastSent : WG.M Int64) from
    hoare_liftAmbient (AmbientM.hiddenClock64 .respLastSent) (Input cs loans))
  intro now
  rw [←bind_assoc]
  apply hoare_bind _ _ (lastSent pid now)
  intro _
  apply hoare_bind _ _ (join _ (create_boundary pid) (create_entry pid))
  intro created
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .respCreated created.isSome) (Input cs loans))
  intro ready
  cases ready with
  | false => exact hoare_consequence (preserves_pure ()) (fun _ hi => hi.1) (fun _ _ hi => hi)
  | true =>
    cases created with
    | none =>
      exact hoare_consequence (hoare_liftAmbient (AmbientM.invariant "unreachable") (Boundary cs loans))
        (fun _ hi => hi.1) (fun _ _ hi => hi)
    | some msg =>
      apply hoare_bind _ _ (join _ (mac_boundary pid msg) (mac_entry pid msg))
      intro bytes
      apply hoare_bind _ _ (session pid)
      intro begun
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .respSessionBegun begun) (Boundary cs loans))
      intro active
      cases active with
      | false => exact preserves_pure ()
      | true => exact suffix pid bytes

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse
