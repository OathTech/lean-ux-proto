import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerReceiveTail

/-! Native endpoint and handshake entry facts are transported on the same
run as the exact peer-reference account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

def Input (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  ExactBoundary cs loans w ∧ HandshakeEntry.Entry w

def Selected (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => ExactBoundary cs loans w
  | some pid => ∃owner : Owner, owner.slot=pid ∧ ExactBoundary cs (owner::loans) w

theorem join (action : WG.M α) (account : Preserves (ExactBoundary cs loans) action)
    (entry : Preserves HandshakeEntry.Entry action) : Preserves (Input cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp entry w a x v b hi.2 run⟩

theorem dst_reset (pid : PeerId) : Preserves (Account holders cs loans) (dstCacheReset pid) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.dstCacheReset_frame) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.dstCacheReset_view) pid)

theorem endpoint_account (pid : PeerId) (endpoint : Endpoint) :
    Preserves (Account holders cs loans) (setPeerEndpoint pid endpoint) := by
  have write : Preserves (Account holders cs loans) (do
      setPeer pid {(←getPeer pid) with endpoint:=some endpoint}
      dstCacheReset pid) := by
    simpa only [bind_assoc] using preserves_bind
      (Account.update
        pid (fun p => {p with endpoint:=some endpoint})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        (fun _ _ h => h) (fun _ => rfl)) (fun _ => dst_reset pid)
  have record (d : Decision) (b : Bool) : Preserves (Account holders cs loans) (branch d b : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch d b) _
  unfold setPeerEndpoint
  simp only [requireNotPending,pure_bind]
  apply preserves_bind (read pid)
  intro p
  apply preserves_bind (store (endpointEq_sameStore endpoint p.endpoint))
  intro eq
  apply preserves_bind (record _ _)
  intro same
  cases same with
  | true => exact preserves_pure _
  | false =>
    apply preserves_bind (record _ _)
    intro v4
    cases v4 with
    | true => exact write
    | false =>
      apply preserves_bind (record _ _)
      intro v6
      cases v6 with
      | true => exact write
      | false => exact preserves_pure _


theorem endpoint_from_skb (pid : PeerId) (src : SkbSource) :
    Preserves (Account holders cs loans) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head setPeerEndpoint; exact endpoint_account _ _)
    | (rx_retention_head getPeer; exact read _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem endpoint (pid : PeerId) (src : SkbSource) :
    Preserves (Input cs loans) (setPeerEndpointFromSkb pid src) :=
  join _ (boundary (fun _ => endpoint_from_skb pid src)) (HandshakeEntry.endpoint pid src)

theorem input_store {action : WG.M α} (same : SameWGStore action) : Preserves (Input cs loans) action := by
  apply join
  · exact boundary (fun _ => store same)
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.store) action same
    · exact CurrentSlots.view_preserves (project := id) (Affiliation.kernel (project := id) same)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
