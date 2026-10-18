import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverReceive

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins Origins.Retaining ConfiguredTraffic

theorem carrier_read_peer (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (getPeer pid) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredRemoval.«0».Leanux.Proofs.WG.ConfiguredRemoval.read) pid)
    (readPeer_native pid confirmed)

theorem carrier_update (pid : PeerId) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  carrier_frame confirmed (ConfiguredIdentity.modifyPeer_view pid f configured)
    (peerUpdate_native pid f slots confirmed)

theorem carrier_key_put (kid : Option KeypairId) (now : Bool) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (keypairPut kid now) :=
  carrier_frame confirmed (ConfiguredIdentity.keypairPut_view kid now)
    (keypairPut_native kid now confirmed)

theorem carrier_counter (kid : KeypairId) (nonce : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (counterValidate kid nonce) := by
  apply carrier_join confirmed _ (counter_native kid nonce confirmed)
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head setKeypair; exact ConfiguredRemoval.frame (ConfiguredIdentity.setKeypair_view _ _))
    | configured_traffic_step

theorem carrier_drop (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (dropRxQueue pid) := by
  apply carrier_join confirmed _ (drop_native pid confirmed)
  apply ConfiguredRemoval.frame
  intro initial
  change Framing.Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold dropRxQueue
  repeat' configured_step initial

theorem carrier_modify (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (front : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (peers : ∀ d, (f d).peers = d.peers) (keys : ∀ d, (f d).keypairs = d.keypairs)
    (confirmed : List Nat) : Framing.Preserves (Carrier confirmed) (modifyDev f) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredRemoval.«0».Leanux.Proofs.WG.ConfiguredRemoval.modifyDevice) f configured)
    (modify_native f front peers keys confirmed)

macro "responder_carrier_poll_step " confirmed:term : tactic => `(tactic| first
  | (receive_update_head setPeer; apply carrier_update; all_goals (intro p; rfl))
  | (rx_retention_head modifyDev; apply carrier_modify; all_goals (intro d; rfl))
  | (rx_retention_head counterValidate; exact carrier_counter _ _ $confirmed)
  | (rx_retention_head dropRxQueue; exact carrier_drop _ $confirmed)
  | (rx_retention_head PrevQueue.peek; exact carrier_store (prevQueuePeek_sameWGStore _) $confirmed)
  | (rx_retention_head endpointFromSkb; exact carrier_store (endpointFromSkb_sameWGStore _) $confirmed)
  | (rx_retention_head getPeer; exact carrier_read_peer _ $confirmed)
  | (rx_retention_head keypairPut; exact carrier_key_put _ _ $confirmed)
  | (rx_retention_head peerPut; exact carrier_peer_put _ $confirmed)
  | (rx_retention_head getRxSkb; exact carrier_skb _ $confirmed)
  | (rx_retention_head freeRxSkb; exact carrier_skb _ $confirmed)
  | (rx_retention_head liftSkb; exact carrier_skb _ $confirmed)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
