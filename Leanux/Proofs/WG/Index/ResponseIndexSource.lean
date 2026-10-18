import Leanux.Proofs.WG.Index.ResponseIndexFrames
import Leanux.Proofs.WG.Index.ReachedIndexSource
import Leanux.Proofs.WG.Index.SelectedSendRetirementEffects
import Leanux.Proofs.WG.Index.ResponseSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem createResponse_endpointBounds (pid : PeerId) :
    Ensures (createResponse pid)
      (fun g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d)
      (fun _ g => ∀ d,g.dev=some d → InitializedBounds.EndpointBounds d) := by
  apply createResponse_preserves_source pid _
  · intro ck hash; exact endpointBounds_modifyPeer pid _ (fun _ => rfl)
  · intro secret; exact endpointBounds_modifyPeer pid _ (fun _ => rfl)
  · exact endpointBounds_modifyPeer pid _ (fun _ => rfl)
  · exact creatorPublish_device_predicate pid InitializedBounds.EndpointBounds
      (fun d _ pre => endpointBounds_affiliation d _ rfl pre)

theorem sendResponse_preserves_source (pid : PeerId) (P Q : WGWorld → Prop)
    (drop : ∀ g,P g → Q g)
    (lastBefore : ∀ now,Ensures (modifyPeer pid fun p => {p with lastSentHandshake := now}) P (fun _ => P))
    (create : Ensures (createResponse pid) P (fun _ => P))
    (mac : ∀ msg,Ensures (addMacToPacket pid msg) P (fun _ => P))
    (session : Ensures (beginSession pid) P (fun _ => Q))
    (derived : Ensures (timersSessionDerived pid) Q (fun _ => Q))
    (traversal : Ensures (timersTraversal pid) Q (fun _ => Q))
    (sent : Ensures (timersAnyAuthenticatedPacketSent pid) Q (fun _ => Q))
    (lastAfter : ∀ now,Ensures (modifyPeer pid fun p => {p with lastSentHandshake := now}) Q (fun _ => Q))
    (send : ∀ msg,Ensures (sendBufferToPeer pid msg) Q (fun _ => Q)) :
    Ensures (sendHandshakeResponse pid) P (fun _ => Q) := by
  have pureQ : Ensures (pure () : WG.M Unit) Q (fun _ => Q) := by
    intro g a r out b pre run; cases run; exact pre
  have clock (R : WGWorld → Prop) (site : HiddenSite) :
      Ensures (hiddenClock64 site : WG.M Int64) R (fun _ => R) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 site) R)
  have branchP (R : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) R (fun _ => R) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) R)
  rw [← Origins.HandshakeSources.response_original]
  unfold Origins.HandshakeSources.responseWith Origins.HandshakeSources.original
  refine ensures_bind _ _ (clock P _) ?_
  intro now
  refine ensures_bind _ _ (lastBefore now) ?_
  intro _
  refine ensures_bind _ _ create ?_
  intro created
  refine ensures_bind _ _ (branchP P _ _) ?_
  intro ready
  cases ready with
  | false =>
    intro g a r out b pre run
    exact pureQ g a r out b (drop g pre) run
  | true =>
    cases created with
    | none =>
      intro g a r out b pre run
      simp [invariant,AmbientM.invariant] at run
      cases run
    | some msg =>
      refine ensures_bind _ _ (mac msg) ?_
      intro bytes
      refine ensures_bind _ _ session ?_
      intro begun
      refine ensures_bind _ _ (branchP Q _ _) ?_
      intro active
      cases active with
      | false => exact pureQ
      | true =>
        refine ensures_bind _ _ derived ?_
        intro _
        refine ensures_bind _ _ traversal ?_
        intro _
        refine ensures_bind _ _ sent ?_
        intro _
        refine ensures_bind _ _ (clock Q _) ?_
        intro now
        exact ensures_bind _ _ (lastAfter now) (fun _ => send bytes)

theorem createResponse_indexPrefix (pid : PeerId) :
    Ensures (createResponse pid) (ResponseIndexPrefix pid) (fun _ => ResponseIndexPrefix pid) := by
  intro g a value out b pre run
  have compatible := createResponse_owner_compatible pid g a value out b pre.2.1 run
  have slots := createResponse_hashSlots_retirement [] pid g a value out b pre.2.2 run
  exact ⟨createResponse_endpointBounds pid g a value out b pre.1 run,compatible,slots⟩

theorem beginSession_indexPrefix (pid : PeerId) :
    Ensures (beginSession pid) (ResponseIndexPrefix pid) (fun _ => ResponseIndexState) := by
  intro g a value out b pre run
  have state := beginSession_endpoint_hashSlots pid g a value out b
    ⟨pre.1,fun d device => (pre.2.1 d device).1,pre.2.2.1⟩ run
  have retirement := beginSession_endpoint_retirement [] pid g a value out b
    ⟨pre.1,fun d device => (pre.2.1 d device).1,pre.2.2.2⟩ run
  exact fun d device => ⟨state.2 d device,state.1 d device,retirement d device⟩

theorem sendHandshakeResponse_indexState (pid : PeerId) :
    Ensures (sendHandshakeResponse pid) (ResponseIndexPrefix pid) (fun _ => ResponseIndexState) := by
  apply sendResponse_preserves_source pid _ _
  · exact fun _ pre d device => ⟨pre.2.2.1 d device,(pre.2.1 d device).1,pre.2.2.2 d device⟩
  · intro now
    exact responsePrefix_sender_frame pid _
      (endpointBounds_modifyPeer pid _ (fun _ => rfl))
      (sender_modifyPeer pid _ (fun _ => rfl))
  · exact createResponse_indexPrefix pid
  · intro msg
    exact responsePrefix_sender_frame pid _
      (endpointBounds_view_frame _ (addMacToPacket_spec_affiliation_variant pid msg))
      (sender_mac pid msg)
  · exact beginSession_indexPrefix pid
  · exact responseIndex_sender_frame _ (sender_derived pid)
  · exact responseIndex_sender_frame _ (sender_traversal pid)
  · exact responseIndex_sender_frame _ (sender_delTimer pid .sendKeepalive)
  · intro now
    exact responseIndex_sender_frame _ (sender_modifyPeer pid _ (fun _ => rfl))
  · intro msg
    exact responseIndex_sender_frame _ (sender_fields_socket pid msg)

namespace Reached

theorem response_core (cs : Ledger) (paid : Owner) (loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (result : Unit)
    (input : HandshakeResponse.Input cs (paid :: loans) w)
    (bounds : InitializedBounds.EndpointSafe (Campaign2.snapshot w a))
    (core : Core w)
    (run : ((sendHandshakeResponse paid.slot).run w).run a = .ok ((result,v),b)) :
    Core v := by
  obtain ⟨holders,funded,stable⟩ := input.1
  have compatible := funded_send_handshakeCompatible holders cs paid loans w
    (HandshakeEntry.entry_facts input.2).1 funded
    (fun d device => (core d device).2.2.1)
  have state := sendHandshakeResponse_indexState paid.slot w a result v b
    ⟨bounds,compatible,fun d device => (core d device).2.1,
      fun d device => (core d device).2.2.2⟩ run
  have tables := sendHandshakeResponse_tables paid.slot w a result v b
    (fun d device => (core d device).1) run
  exact fun d device => ⟨tables d device,(state d device).1,(state d device).2⟩

theorem response_native (cs : Ledger) (paid : Owner) (loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (result : Unit)
    (input : HandshakeResponse.Input cs (paid :: loans) w)
    (bounds : InitializedBounds.EndpointSafe (Campaign2.snapshot w a))
    (base : BaseCoherence.Inv w) (core : Core w)
    (run : ((sendHandshakeResponse paid.slot).run w).run a = .ok ((result,v),b)) :
    HandshakeResponse.Input cs (paid :: loans) v ∧ BaseCoherence.Inv v ∧ Core v := by
  have account := (hoare_iff_run_ambient _ _ _).mp (HandshakeSendResponse.sendResponse paid.slot)
    w a result v b input run
  have entry := (hoare_iff_run_ambient _ _ _).mp (HandshakeReceiveSlots.sendResponse paid.slot)
    w a result v b input.2 run
  have baseAfter := BaseCoherence.transport base
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.sendHandshakeResponse_view paid.slot)
      w a result v b run)
  exact ⟨⟨account,entry⟩,baseAfter,response_core cs paid loans w v a b result input bounds core run⟩

theorem response_reached_normal
    (initial : Ledger) (paid : Owner) (loans : Reservations)
    (before history : List RxHistory.Event) (w : World)
    (v : WGWorld) (after : Ambient) (result : Unit)
    (entry : Aux initial (paid :: loans) before history w)
    (run : ((sendHandshakeResponse paid.slot).run w.wg).run w.ambient = .ok ((result,v),after)) :
    ∃ suffix, history = before ++ suffix ∧
      HandshakeResponse.Input (remaining initial (NapiCarrier.removedPackets suffix))
        (paid :: loans) v ∧ BaseCoherence.Inv v ∧ Core v := by
  obtain ⟨suffix,holders,hist,funded,stable⟩ := aux_funded entry
  refine ⟨suffix,hist,?_⟩
  exact response_native _ paid loans w.wg v w.ambient after result
    ⟨⟨holders,funded,stable⟩,HandshakeEntry.of_owner entry.1.2.1 entry.1.2.2⟩
    (aux_bounds entry) entry.2.1 entry.2.2 run

end Reached

end Leanux.Proofs.WG.Index
