import Leanux.Proofs.WG.Queues.HandshakeReceive
import Leanux.Proofs.WG.Queues.CurrentSlotTraffic

/-! Three-slot compatibility survives the actual handshake consumers. Owner
acquisition and final payment reuse the existing source-aware slot contracts. -/
namespace Leanux.Proofs.WG.HandshakeSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Affiliation CurrentSlots Queues Queues.RxCredits

theorem pubkeyLookup (key : Key) : Preserves CurrentSlots.Inv (WG.pubkeyLookup key) := by
  unfold WG.pubkeyLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head peerGetMaybeZero
       exact CurrentSlots.view_preserves (project := id) (Affiliation.peerGetMaybeZero_view _))
    | slot_traffic_step

private theorem initiationOut (peer ret : Option PeerId) :
    Preserves CurrentSlots.Inv (HandshakeLoans.initiationOut peer ret) := by
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' slot_traffic_step

private theorem initiationTail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) :
    Preserves CurrentSlots.Inv (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiationOut _ _)
    | receive_crypto CurrentSlots.Inv
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | slot_traffic_step

private theorem initiationAfterLookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Preserves CurrentSlots.Inv (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiationOut _ _)
    | (rx_retention_head HandshakeLoans.initiationTail; exact initiationTail _ _ _ _ _ _)
    | slot_traffic_step

theorem consumeInitiation (msg : List UInt8) : Preserves CurrentSlots.Inv (WG.consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiationOut _ _)
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact initiationAfterLookup _ _ _ _ _)
    | (rx_retention_head WG.pubkeyLookup; exact pubkeyLookup _)
    | receive_crypto CurrentSlots.Inv
    | slot_traffic_step

private theorem responseTail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Preserves CurrentSlots.Inv (HandshakeLoans.responseTail msg identity pid) := by
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | receive_crypto CurrentSlots.Inv
    | slot_traffic_step

theorem consumeResponse (msg : List UInt8) : Preserves CurrentSlots.Inv (WG.consumeResponse msg) := by
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact responseTail _ _ _)
    | (rx_retention_head WG.indexLookup; exact CurrentSlots.indexLookup_preserves _ _)
    | slot_traffic_step

theorem cookieMessageConsume (msg : List UInt8) : Preserves CurrentSlots.Inv (WG.cookieMessageConsume msg) := by
  unfold WG.cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head WG.indexLookup; exact CurrentSlots.indexLookup_preserves _ _)
    | slot_traffic_step

end Leanux.Proofs.WG.HandshakeSlots
