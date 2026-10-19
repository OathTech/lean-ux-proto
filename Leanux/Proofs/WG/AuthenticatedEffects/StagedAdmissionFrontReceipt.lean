import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontCharge
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationBirthHistory

/-! The actual routed receipt appends precisely its canonical birth tickets
at its actual journal position, after any counted overflow. A refusal creates
no packet birth. All preexisting terminal outcomes are retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

abbrev Input := HandshakeSecurity.StagedConservation.Front.Input

def routedEvent (input : Input) (r : WGRunWitness (Except Int PeerId)) : Event :=
  .old (.routed input.family input.address input.packets input.mtu r)

theorem Checkpoint.canonical (cut : Checkpoint entry history ledger snapshot)
    (canonical : entry.births = Staged.Obligations.births entry.history) :
    Staged.Obligations.births history = entry.births := by
  cases cut with
  | initial => exact canonical.symm
  | nonfinal => exact (births_quiet _ rfl).trans canonical.symm
  | released => exact (births_quiet _ rfl).trans canonical.symm
  | trimmed => exact (births_quiet _ rfl).trans canonical.symm

def Normal (entry : Entry) (input : Input) (r : WGRunWitness (Except Int PeerId))
    (history : List Event) (ledger : Ledger) : Prop :=
  r.Valid (Packets.txFront input.family input.address input.packets input.mtu) ∧
  Valid (Staged.Obligations.births (history ++ [routedEvent input r])) ledger ∧
  QueueInv (history ++ [routedEvent input r]) ledger r.after ∧
  (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ entry.ledger →
    (ticket,Status.terminal outcome) ∈ ledger) ∧
  ∃ prior snapshot, Checkpoint entry history prior snapshot ∧
    match r.value with
    | .error _ => ledger = prior ∧ QueueInv history prior r.after
    | .ok pid => ∃ w a generation stamp,
      QueueInv history prior w ∧
      ((Lifetimes.xmitSplice pid (input.packets.map (fun p => {p with mtu := input.mtu}))).run w).run a =
        .ok (((),r.after),r.ambientAfter) ∧
      ledger = appendBirths prior history.length (.staged generation pid stamp)
        (input.packets.map (fun p => {p with mtu := input.mtu}))

/-- Native validity and the actual observed body's postcondition are the only
source premises. The native intermediate cuts are not supplied by the caller. -/
theorem completed (input : Input) (r : WGRunWitness (Except Int PeerId))
    (run : r.Valid (Packets.txFront input.family input.address input.packets input.mtu))
    (canonical : entry.births = Staged.Obligations.births entry.history)
    (post : BodyPost entry input.packets input.mtu r.value history r.after r.ambientAfter) :
    ∃ ledger, Normal entry input r history ledger := by
  cases selected : r.value with
  | error code =>
    simp only [BodyPost,selected] at post
    obtain ⟨prior,snapshot,cut,queues⟩ := post
    have domain := cut.canonical canonical
    have noBirth : birthPackets (routedEvent input r) = [] := by simp [routedEvent,birthPackets,selected]
    have valid := cut.accounted.2.1
    rw [←domain,←births_quiet history noBirth] at valid
    exact ⟨prior,run,valid,queues.append_history _,
      fun _ _ member => cut.accounted.1.terminal member,
      prior,snapshot,cut,by rw [selected]; exact ⟨rfl,queues⟩⟩
  | ok pid =>
    simp only [BodyPost,selected] at post
    obtain ⟨w,a,⟨prior,snapshot,cut,queues⟩,spliceRun⟩ := post
    let added := input.packets.map (fun p => {p with mtu := input.mtu})
    let splice : WGRunWitness Unit := ⟨(),w,r.after,a,r.ambientAfter⟩
    obtain ⟨d,p,device,resident,changed,charge⟩ := Staged.splice pid added splice spliceRun
    dsimp only [splice] at device changed
    have epoch : Packets.epoch w = some d.ifindex := by simp [Packets.epoch,device]
    have sameEpoch : Packets.epoch r.after = Packets.epoch w := by
      simp only [Packets.epoch,changed,device,Option.map_some]
    have old : Staged.stagedAt w pid = some (p.internalId,p.staged) := by
      simp [Staged.stagedAt,device,resident]
    have after : Staged.stagedAt r.after pid = some (p.internalId,p.staged ++ added) := by
      simp [Staged.stagedAt,changed]
    have others : ∀ other, pid ≠ other → Staged.stagedAt r.after other = Staged.stagedAt w other := by
      intro other different
      simp [Staged.stagedAt,changed,device,Std.TreeMap.getElem?_insert,different]
    let receipt : Journal.RoutingHistory.Receipt := ⟨input.family,input.address,input.packets,input.mtu,r⟩
    have born := routed_births receipt run selected (sameEpoch.trans epoch) after history
    obtain ⟨valid,bounded,next,retained⟩ := admission cut.accounted.2.1 cut.accounted.2.2.1
      queues epoch sameEpoch old after others born
    have domain : Staged.Obligations.births (history ++ [routedEvent input r]) =
        entry.births ++ freshTickets history.length 0 added := by
      rw [births_emit,cut.canonical canonical]
      simp only [routedEvent,birthPackets,selected,added]
    rw [←domain] at valid
    refine ⟨_,run,valid,next,?_,prior,snapshot,cut,?_⟩
    · intro ticket outcome member
      exact retained ticket outcome (cut.accounted.1.terminal member)
    · rw [selected]
      exact ⟨w,a,d.ifindex,p.internalId,queues,spliceRun,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
