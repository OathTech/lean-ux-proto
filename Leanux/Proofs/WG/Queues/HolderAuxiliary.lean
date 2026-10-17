import Leanux.Proofs.WG.Queues.HolderScheduler
import Leanux.Proofs.WG.Queues.SessionCarrier
import Leanux.Proofs.WG.Queues.CurrentSlotFrames
import Leanux.Proofs.WG.Origins.OwnerEnvironment

/-! The existing owner journal already carries configured identity, RX owner
bounds and packet freshness. Three-slot compatibility is an additional state
fact. Their conjunction is transported on one original observer execution. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAuxiliary
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Packet freshness follows from the existing allocation invariant, including
its absent-device case; it is not a new runner input. -/
theorem allocation_packets (hi : AllocationInv h w) : Packets.Inv w := by
  cases hd : w.dev with
  | none => simp [Packets.Inv,Packets.snapshot,hd,Bounded]
  | some d => simpa only [Packets.Inv,Packets.snapshot,hd] using hi.packetBounded d hd

theorem owner_configured (hi : OwnerChecks.Inv h w) : ConfiguredIdentity.Inv w.wg :=
  hi.current.2.1.1

theorem owner_packets (hi : OwnerChecks.Inv h w) : Packets.Inv w.wg :=
  allocation_packets hi.allocation

/-- This adds the required auxiliary state to the same committed accounting
cut. It asserts no initialized reachability or totality. -/
def Inv (initial : Ledger) (loans : Reservations) (before h : List RxHistory.Event)
    (w : World) : Prop :=
  HolderScheduler.Inv initial loans before h w ∧ OwnerChecks.Inv h w ∧ CurrentSlots.Inv w.wg

theorem entry (hi : Inv initial loans before h w) :
    ConfiguredIdentity.Inv w.wg ∧ OwnerBounds.Carrier w.wg ∧
      CurrentSlots.Inv w.wg ∧ Packets.Inv w.wg :=
  ⟨owner_configured hi.2.1,hi.2.1.carrier,hi.2.2,owner_packets hi.2.1⟩

/-- Each obligation uses the same actual observer and complete incoming
history. A Stop retains the existing owner safety and never invents a state. -/
theorem pair (action : RxHistory.Obs α)
    (account : PrefixPreserves (HolderScheduler.Inv initial loans before) (fun _ => True) action)
    (owner : OwnerChecks.Preserves action)
    (slots : ∀ w h, Inv initial loans before h w → ∀ x v,
      (runPrefix action w h).1 = .ok (x,v) → CurrentSlots.Inv v.wg) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe action := by
  intro w h hi
  obtain ⟨suffix,history,safe,post⟩ := owner w h hi.2.1
  have held := (account w h hi.1).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix action w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at held post
    exact ⟨held,post,slots w h hi out.1 out.2 run⟩

theorem store (hi : Inv initial loans before h w)
    (same : productStoreView v = productStoreView w) : Inv initial loans before h v := by
  have dev : v.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43 => p.2.2.2.dev) same
  refine ⟨HolderScheduler.store hi.1 same,OwnerWorkers.store h w v same hi.2.1,?_⟩
  apply CurrentSlots.fields_transport hi.2.2
  unfold CurrentSlots.fields Leanux.Proofs.WG.Queues.RxCredits.keyWords
  rw [dev]

/-- The actual native session adds no RX removal event, even when its lifetime
journal stops partway through. All old journal entries remain in place. -/
theorem session_quiet (pid : PeerId) : HistoryFrame NapiCarrier.removed
    (Origins.HistoryAdapters.session pid) := by
  intro w h
  unfold Origins.HistoryAdapters.session Origins.HistoryAdapters.focus
  exact focusPrefix_other Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    NapiCarrier.removed (fun e => by cases e <;> rfl) _ w h

/-- Session installation uses the configured self word and three actual slots
from this entry. Funding, physical ring and owner history share its exact
native WG/Ambient endpoints, including normal false/refusal results. -/
theorem session_normal (pid : PeerId) (hi : Inv initial loans before h w)
    (run : runPrefix (Origins.HistoryAdapters.session pid) w h = (.ok (result,v),k)) :
    Inv initial loans before k v := by
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    (beginSession pid) w v result
    ((Origins.HistoryAdapters.session_erases pid w h).symm.trans (congrArg Prod.fst run))
  have owners := (OwnerChecks.session pid w h hi.2.1).choose_spec.2.2
  rw [run] at owners
  obtain ⟨old,history,holders,funded,stable⟩ := hi.1.1
  have post := SessionCarrier.beginSession_funded pid funded stable
    (owner_configured hi.2.1) hi.2.1.carrier hi.2.2 w.ambient v.ambient native
  have account : HolderNapi.At initial loans before k v :=
    HolderDecryptHistory.quiet_cut (Appends.focus _ _ _) (session_quiet pid) history run
      ⟨holders,post.1,post.2.1⟩
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.beginSession_cell pid)
    w.wg w.ambient result v.wg v.ambient native
  obtain ⟨epoch,n,events,ring,refines,cell⟩ := hi.1.2
  exact ⟨⟨account,epoch,n,events,ring,refines,same.trans cell⟩,owners,post.2.2.2.2⟩

theorem session_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (Origins.HistoryAdapters.session pid) := by
  intro w h hi
  obtain ⟨suffix,history,safe,_⟩ := OwnerChecks.session pid w h hi.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix (Origins.HistoryAdapters.session pid) w h).1 with
  | error e => trivial
  | ok out => exact session_normal pid hi (Prod.ext run rfl)

end Leanux.Proofs.WG.Queues.RxCredits.HolderAuxiliary
