import Leanux.Proofs.WG.RetirementSecurity.TxWorkKeyFrames

/-! Native handshake lookup and consumption preserve pending TX work even
when nullable owner bookkeeping changes or an empty peer is finally released. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem peer_get_maybe_work (pid : Option PeerId) : SameView queued (peerGetMaybeZero pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold peerGetMaybeZero refcountIncNotZero
  simp only [requireNotPending,branch,branchCmp,unsupported,invariant]
  repeat' key_work_step initial

theorem acquire_owner_work (owner : IndexOwner) : SameView queued (Affiliation.acquireOwner owner) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold Affiliation.acquireOwner
  repeat' first
    | (rx_retention_head peerGetMaybeZero; exact (peer_get_maybe_work _).wp (·=initial))
    | (rx_retention_head IndexOwner.setPeerWord
       cases owner <;> unfold IndexOwner.setPeerWord <;> repeat' key_work_step initial)
    | key_work_step initial

macro "handshake_work_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerPut; exact (peer_put _).wp (·=$initial))
  | (rx_retention_head peerGetMaybeZero; exact (peer_get_maybe_work _).wp (·=$initial))
  | key_work_step $initial)

theorem index_lookup_work (kinds : List IndexKind) (index : Nat) : SameView queued (indexLookup kinds index) := by
  intro initial
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · exact (index_work _).wp (·=initial)
  · intro owner
    exact (acquire_owner_work owner).wp (·=initial)

theorem pubkey_lookup_work (key : Key) : SameView queued (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | handshake_work_step initial

theorem initiation_out_work (peer ret : Option PeerId) : SameView queued (HandshakeLoans.initiationOut peer ret) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | handshake_work_step initial

theorem initiation_tail_work (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) : SameView queued (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_work _ _).wp (· = initial))
    | handshake_work_step initial

theorem initiation_lookup_work (msg e ck hash : List UInt8) (peer : Option PeerId) : SameView queued (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_work _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationTail; exact (initiation_tail_work _ _ _ _ _ _).wp (· = initial))
    | handshake_work_step initial

theorem consume_initiation_work (msg : List UInt8) : SameView queued (consumeInitiation msg) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_work _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact (initiation_lookup_work _ _ _ _ _).wp (· = initial))
    | (rx_retention_head pubkeyLookup; exact (pubkey_lookup_work _).wp (· = initial))
    | handshake_work_step initial

theorem response_tail_work (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) : SameView queued (HandshakeLoans.responseTail msg identity pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | handshake_work_step initial

theorem consume_response_work (msg : List UInt8) : SameView queued (consumeResponse msg) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact (response_tail_work _ _ _).wp (· = initial))
    | (rx_retention_head indexLookup; exact (index_lookup_work _ _).wp (· = initial))
    | handshake_work_step initial

theorem cookie_consume_work (msg : List UInt8) : SameView queued (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (index_lookup_work _ _).wp (· = initial))
    | handshake_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
