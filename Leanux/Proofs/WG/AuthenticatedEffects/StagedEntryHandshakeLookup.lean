import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveLookup

/-! Handshake lookup borrows and owner-word writes retain the full entry
view, including arbitrary failed maybe-zero acquisitions. No initialized
reference positivity is needed for these projected native frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeLookup
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity
set_option maxHeartbeats 600000

theorem borrowed (result : Option PeerId)
    (same : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    StagedEntry.view v = StagedEntry.view w := by
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at same
    have device : v.dev = w.dev := congrArg WGStoreView.dev same
    change StagedEntry.view {dev := v.dev} = StagedEntry.view {dev := w.dev}
    rw [device]
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := same
    change w.dev = some d at device
    have same := congrArg WGStoreView.dev after
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at same
    change StagedEntry.view {dev := v.dev} = _
    rw [same]
    exact Queued.replace_peer device resident (q := {p with refcount := p.refcount+1}) rfl rfl rfl

theorem maybe_peer (peer : Option PeerId) : SameView StagedEntry.view (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact borrowed result ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w a result v b rfl run).2

theorem public_lookup (key : Key) : SameView StagedEntry.view (pubkeyLookup key) := by
  unfold pubkeyLookup
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro device
  apply SameView.bind (TimerFrames.branch_frame _ _)
  intro ignored
  exact maybe_peer _

theorem set_key (kid : KeypairId) (key : Keypair) : SameView StagedEntry.view (setKeypair kid key) := by
  unfold setKeypair
  exact ReceiveFrames.device (fun d => {d with keypairs := d.keypairs.insert kid key})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem owner_write (owner : IndexOwner) (peer : Option PeerId) :
    SameView StagedEntry.view (owner.setPeerWord peer) := by
  cases owner with
  | handshake pid => exact Queued.update pid (fun p => {p with handshakeEntryPeer := peer}) (fun _ => ⟨rfl,rfl,rfl⟩)
  | keypair kid =>
    change SameView StagedEntry.view (getKeypair kid >>= _)
    exact SameView.bind (ReceiveFrames.key_read kid) (fun key => set_key kid _)

theorem acquire_owner (owner : IndexOwner) : SameView StagedEntry.view (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  apply SameView.bind (fun initial => indexOwner_peerWord_preserves owner (fun w => StagedEntry.view w = initial))
  intro peer
  apply SameView.bind (maybe_peer peer)
  intro acquired
  exact SameView.bind (owner_write owner acquired) (fun _ => SameView.pure _ _)

theorem index_lookup (kinds : List IndexKind) (number : Nat) :
    SameView StagedEntry.view (indexLookup kinds number) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact (acquire_owner _).wp (· = initial))
    | (rx_retention_head liftIndex; exact (TimerFrames.store (indexBucket_sameStore number)).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => StagedEntry.view w = initial)
       intro x b
       change Preserves (fun w => StagedEntry.view w = initial) _)
    | rxstack_preserves_join
    | entry_timer_native_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeLookup
