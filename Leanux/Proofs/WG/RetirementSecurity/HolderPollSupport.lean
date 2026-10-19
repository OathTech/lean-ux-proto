import Leanux.Proofs.WG.RetirementSecurity.HolderReplayFrames
import Leanux.Proofs.WG.Origins.CurrentStack
import Leanux.Proofs.WG.Queues.BaseCoherenceStack

/-! Independent native support for the key-credit poll phases. The fixed
session history, physical packet occurrences and live base publication are
transported on the original source; no key balance is inferred from them. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits CurrentPoll

def Support (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (w : WGWorld) : Prop :=
  OccurrenceStack.Ready locals active w ∧ CurrentLifecycle.Inv sessions w ∧
    BaseCoherence.Inv w ∧ KeySlotLiveness.Inv w

theorem join {action : WG.M α}
    (physical : Preserves (OccurrenceStack.Ready locals active) action)
    (current : Preserves (CurrentLifecycle.Inv sessions) action)
    (structural : SameView BaseCoherence.view action)
    (live : Preserves KeySlotLiveness.Inv action) : Preserves (Support sessions locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp current w a result v b before.2.1 run,
    BaseCoherence.transport before.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp structural w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp live w a result v b before.2.2.2 run⟩

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Support sessions locals active) action :=
  join (RxPollOccurrences.store same)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentLifecycle.«0».Leanux.Proofs.WG.CurrentLifecycle.store_preserves) action same sessions)
    (BaseCoherence.store_view same) (KeySlotLiveness.store same)

theorem peek (pid : PeerId) : Preserves (Support sessions locals active) (peekRxQueue pid) :=
  join (RxPollOccurrences.peek pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.peek_preserves) pid sessions)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceStack.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.peek_structure) pid)
    (KeySlotLiveness.poll_peek pid)

theorem drop (pid : PeerId) : Preserves (Support sessions locals active) (dropRxQueue pid) :=
  join (RxPollOccurrences.drop pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.drop_preserves) pid sessions)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceStack.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.drop_structure) pid)
    (KeySlotLiveness.poll_drop pid)

theorem complete (pid : PeerId) : Preserves (Support sessions locals active) (completeRxQueue pid) :=
  join (RxPollOccurrences.complete pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.complete_preserves) pid sessions)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceStack.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.complete_structure) pid)
    (KeySlotLiveness.poll_complete pid)

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Support sessions locals active) (counterValidate kid nonce) :=
  join (RxPollOccurrences.counter kid nonce) (CurrentRx.counterValidate_preserves kid nonce sessions)
    (BaseCoherence.counterValidate_view kid nonce) (KeySlotLiveness.validate_counter kid nonce)

theorem consume (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Support sessions locals active) (consumeDataDone pid pkt endpoint) :=
  join (RxPollOccurrences.consume pid pkt endpoint) (CurrentRx.consumeDataDone_preserves pid pkt endpoint sessions)
    (BaseCoherence.consumeDataDone_view pid pkt endpoint) (KeySlotLiveness.consume_done pid pkt endpoint)

theorem stack (packets : List (List UInt8)) :
    Preserves (fun w : World=>Support sessions locals active w.wg) (packets.forM Env.deliverInner) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ⟨(hoare_iff_run _ _ _).mp (OccurrenceStack.stackForM_stack packets) w result v before.1 run,
    (hoare_iff_run _ _ _).mp (CurrentStack.stackForM_preserves packets sessions) w result v before.2.1 run,
    BaseCoherence.transport before.2.2.1 ((ProjectedAction.iff_run _ _ _).mp (BaseCoherence.stack_view packets) w result v run),
    (hoare_iff_run _ _ _).mp (KeySlotLiveness.stackForM_stack (pending:=[]) packets) w result v before.2.2.2 run⟩

theorem key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Support sessions locals active) (keypairPut kid now) := by
  apply join (RxPollOccurrences.key_put kid now)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.keyPut_preserves) sessions kid now)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.keyPut_view) kid now)
    (KeySlotLiveness.key_put kid now)

theorem peer_put (pid : Option PeerId) :
    Preserves (Support sessions locals active) (peerPut pid) := by
  apply join (RxPollOccurrences.peer_put pid)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentTraffic.«0».Leanux.Proofs.WG.CurrentTraffic.pay_preserves) sessions pid)
    (BaseCoherence.peerPut_view pid) (KeySlotLiveness.peer_put pid)

theorem free_rx (skb : SkbId) : Preserves (Support sessions locals active) (freeRxSkb skb) := by
  apply join (RxPollOccurrences.free_rx skb)
  · repeat' current_poll_native sessions
  · exact BaseCoherence.skb_view _
  · exact KeySlotLiveness.skb _

theorem cleanup (skb : SkbId) (pkt : RxPacket) (flag : Bool) :
    Preserves (Support sessions locals active) (RxCredits.cleanup skb pkt flag) := by
  unfold RxCredits.cleanup
  apply preserves_bind (key_put _ _)
  intro u
  apply preserves_bind (peer_put _)
  intro u
  apply preserves_bind (show Preserves (Support sessions locals active) (branch .rxPollFree flag) from
    hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (Support sessions locals active))
  intro flag
  exact free_rx _

theorem anchors (before : Support sessions locals active w)
    (funded : holders.Funded carriers loans w) : SlotPeerReferences holders loans w :=
  KeySlotLiveness.references before.2.2.2 funded before.2.2.1 before.2.1.1

theorem stack_keys (account : HolderAccount temporary w.wg)
    (before : Support sessions locals active w.wg) (current : CurrentsCompatible w.wg)
    (packets : List (List UInt8)) (run : (packets.forM Env.deliverInner).run w=.ok ((),v)) :
    HolderAccount temporary v.wg ∧ Support sessions locals active v.wg := by
  have combined : StackOwnership.Ready temporary locals active w.wg :=
    ⟨⟨account,before.1.2⟩,before.1.1,current⟩
  exact ⟨((hoare_iff_run _ _ _).mp (StackOwnership.stackForM_stack packets) w () v combined run).1.1,
    (hoare_iff_run _ _ _).mp (stack packets) w () v before run⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
