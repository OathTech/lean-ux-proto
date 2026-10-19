import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeSend

/-! The real initiation and response arms preserve the exact acquired loan
through endpoint/session work and pay it only at their original receive tail. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

private theorem response_after_lookup (o : Owner) (src : SkbSource) :
    Hoare (HandshakeResponse.afterLookup (some o.slot) src) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ ExactBoundary cs (o::loans) w) := by
  have inner : Hoare (do
      setPeerEndpointFromSkb o.slot src
      HandshakeReceive.responseSession o.slot
      pure (some o.slot) : WG.M (Option PeerId)) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ ExactBoundary cs (o::loans) w) := by
    apply hoare_bind _ _ (endpoint o.slot src)
    intro _
    apply hoare_bind _ _ (hoare_consequence (response_session o.slot)
      (fun w hi => ⟨hi.1,HandshakeEntry.entry_facts hi.2⟩) (fun _ _ hi => hi))
    intro _
    exact hoare_pure _ _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do
    setPeerEndpointFromSkb o.slot src
    HandshakeReceive.responseSession o.slot
    pure (some o.slot) : WG.M (Option PeerId)).run w).run
      (CounterWindow.record a .hsRespNoPeer false)=.ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp inner w _ result v b hi run

theorem response_branch (msg : List UInt8) (src : SkbSource) :
    Hoare (HandshakeResponse.branchSource msg src) (Input cs loans) (Selected cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  unfold HandshakeResponse.branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  obtain ⟨holders,account⟩ := hi.1
  have post := response msg account a c consume
  have entry := (hoare_iff_run_ambient _ _ _).mp (HandshakeEntry.response msg) w a peer u c hi.2 consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsRespNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact ⟨holders,post⟩
  | some pid =>
    obtain ⟨owner,slot,account⟩ := post
    subst pid
    have paid := (hoare_iff_run_ambient _ _ _).mp (response_after_lookup owner src)
      u c result v b ⟨⟨holders,account⟩,entry⟩ tail
    rw [paid.1]
    exact ⟨owner,rfl,paid.2⟩

private theorem initiation_after_lookup (o : Owner) (src : SkbSource) :
    Hoare (HandshakeInitiation.afterLookup (some o.slot) src) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ ExactBoundary cs (o::loans) w) := by
  have inner : Hoare (do
      setPeerEndpointFromSkb o.slot src
      sendHandshakeResponse o.slot
      pure (some o.slot) : WG.M (Option PeerId)) (Input cs (o::loans))
      (fun peer w => peer=some o.slot ∧ ExactBoundary cs (o::loans) w) := by
    apply hoare_bind _ _ (endpoint o.slot src)
    intro _
    apply hoare_bind _ _ (send_response o.slot)
    intro _
    exact hoare_pure _ _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  change ((do
    setPeerEndpointFromSkb o.slot src
    sendHandshakeResponse o.slot
    pure (some o.slot) : WG.M (Option PeerId)).run w).run
      (CounterWindow.record a .hsInitNoPeer false)=.ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp inner w _ result v b hi run

theorem initiation_branch (msg : List UInt8) (src : SkbSource) :
    Hoare (HandshakeInitiation.branchSource msg src) (Input cs loans) (Selected cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  unfold HandshakeInitiation.branchSource at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨peer,u,c,consume,tail⟩ := run
  obtain ⟨holders,account⟩ := hi.1
  have post := (hoare_iff_run_ambient _ _ _).mp (initiation msg) w a peer u c account consume
  have entry := (hoare_iff_run_ambient _ _ _).mp (HandshakeEntry.initiation msg) w a peer u c hi.2 consume
  cases peer with
  | none =>
    change Except.ok ((none,u),CounterWindow.record c .hsInitNoPeer true)=.ok ((result,v),b) at tail
    cases tail
    exact ⟨holders,post⟩
  | some pid =>
    obtain ⟨owner,slot,account⟩ := post
    subst pid
    have paid := (hoare_iff_run_ambient _ _ _).mp (initiation_after_lookup owner src)
      u c result v b ⟨⟨holders,account⟩,entry⟩ tail
    rw [paid.1]
    exact ⟨owner,rfl,paid.2⟩

theorem selected_finish (peer : Option PeerId) (msg : List UInt8) :
    Hoare (HandshakeReceive.finishSelected peer msg) (Selected cs loans peer)
      (fun _ => ExactBoundary cs loans) := by
  cases peer with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    cases run
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    obtain ⟨owner,slot,holders,account⟩ := hi
    subst pid
    exact ⟨holders,(hoare_iff_run_ambient _ _ _).mp (finish_selected owner msg) w a x v b account run⟩

theorem complete (peer : Option PeerId) (msg : List UInt8) :
    Hoare (HandshakeArms.complete peer msg) (Selected cs loans peer)
      (fun _ => ExactBoundary cs loans) := by
  cases peer with
  | none => exact preserves_pure ()
  | some pid => exact selected_finish (some pid) msg

theorem initiation_arm (msg : List UInt8) (src : SkbSource) :
    Hoare (HandshakeArms.initiation msg src) (Input cs loans) (fun _ => ExactBoundary cs loans) := by
  rw [HandshakeArms.initiation_factor]
  exact hoare_bind _ _ (initiation_branch msg src) (fun peer => complete peer msg)

theorem response_arm (msg : List UInt8) (src : SkbSource) :
    Hoare (HandshakeArms.response msg src) (Input cs loans) (fun _ => ExactBoundary cs loans) := by
  rw [HandshakeArms.response_factor]
  exact hoare_bind _ _ (response_branch msg src) (fun peer => complete peer msg)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
