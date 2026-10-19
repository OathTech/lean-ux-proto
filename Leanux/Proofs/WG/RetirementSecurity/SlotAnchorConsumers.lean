import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorLookup

/-! Original handshake consumers retain independent key-slot anchors through
lookup acquisition, authentication/replay rejection, and their real failure
payments. Peer count changes are permitted; no key credit is manufactured. -/
namespace Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (SlotPeerReferences holders loans) action :=
  affiliation (Affiliation.kernel same)

theorem update_then (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId)
    (slots : ∀p,HasKeySlot (f p) → HasKeySlot p)
    (next : ∀x,Preserves (SlotPeerReferences holders loans) (tail x)) :
    Preserves (SlotPeerReferences holders loans) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f stamp slots) next

macro "slot_anchor_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update
     · intro p; rfl
     · intro p h; exact h)
  | (receive_update_head Bind.bind
     apply update_then
     · intro p; rfl
     · intro p h; exact h
     intro x)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head getKeypair; exact store (getKeypair_sameWGStore _))
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rxstack_preserves_join
  | rx_retention_step)

theorem initiation_out (peer ret : Option PeerId) :
    Preserves (SlotPeerReferences holders loans) (HandshakeLoans.initiationOut peer ret) := by
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' slot_anchor_step

theorem initiation_tail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | receive_crypto (SlotPeerReferences holders loans)
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | slot_anchor_step

theorem initiation_after_lookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Preserves (SlotPeerReferences holders loans) (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationTail; exact initiation_tail _ _ _ _ _ _)
    | slot_anchor_step

theorem consume_initiation (msg : List UInt8) :
    Preserves (SlotPeerReferences holders loans) (consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact initiation_after_lookup _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _)
    | receive_crypto (SlotPeerReferences holders loans)
    | slot_anchor_step

theorem response_tail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Preserves (SlotPeerReferences holders loans) (HandshakeLoans.responseTail msg identity pid) := by
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | receive_crypto (SlotPeerReferences holders loans)
    | slot_anchor_step

theorem consume_response (msg : List UInt8) :
    Preserves (SlotPeerReferences holders loans) (consumeResponse msg) := by
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact response_tail _ _ _)
    | (rx_retention_head indexLookup; exact lookup _ _)
    | slot_anchor_step

theorem consume_cookie (msg : List UInt8) :
    Preserves (SlotPeerReferences holders loans) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup _ _)
    | slot_anchor_step

end Leanux.Proofs.WG.RetirementSecurity.SlotAnchors
