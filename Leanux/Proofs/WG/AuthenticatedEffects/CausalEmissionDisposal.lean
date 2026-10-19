import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProduct
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionQuiet

/-! Native staged erasure and reference repayment retain sent occurrences.
Their new source-cut receipts are quiet for both append accounting and prior
delivery certificates; neither theorem infers a socket event from a disposal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open HandshakeSecurity

def contributing? (event : Event) : Option Event :=
  match added event with
  | [] => none
  | _ :: _ => some event

theorem state_quiet_of_frame (body : WGPrefix Event α) (appends : StateAppends body)
    (frame : StateHistoryFrame contributing? body) : StateQuiet body := by
  intro w a h
  obtain ⟨suffix,grown⟩ := appends w a h
  have unchanged := frame w a h
  change (runWGPrefix body w a h).2.filterMap contributing? = h.filterMap contributing? at unchanged
  change (runWGPrefix body w a h).2 = h ++ suffix at grown
  rw [grown,List.filterMap_append] at unchanged
  have empty : suffix.filterMap contributing? = [] :=
    List.append_cancel_left (as := h.filterMap contributing?) (by simpa only [List.append_nil] using unchanged)
  have none := List.filterMap_eq_nil_iff.mp empty
  have emptyAdded : ∀ event ∈ suffix, added event = [] := by
    intro event member
    have quiet := none event member
    unfold contributing? at quiet
    cases result : added event with
    | nil => rfl
    | cons datum rest => rw [result] at quiet; contradiction
  have emptyEmission : emitted suffix = [] := by
    unfold emitted
    exact List.flatMap_eq_nil_iff.mpr emptyAdded
  rw [grown,emitted_append,emptyEmission,List.append_nil]

theorem disposal (body : WGPrefix StagedDisposal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) :
    StateSafe (focusStatePrefix Event.stagedDisposal stagedDisposal? body) :=
  state_observed _ native (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _)
    (focus_state_quiet _ _ (fun _ => rfl) _) frame

theorem peer_release (peer : Option PeerId) : StateSafe (CausalJournal.peerRelease peer) :=
  disposal _ _ (StagedDisposal.release_erases peer) (fun initial => peerPut_sent_spec (· = initial) peer)

theorem staged_purge (pid : PeerId) : StateSafe (CausalJournal.stagedPurge pid) :=
  disposal _ _ (StagedDisposal.purge_erases pid)
    (by sent_frame [purgeStagedPackets] using [getPeer_sent_spec,setPeer_sent_spec])

theorem product_receipt (body : PrefixM Event α) (safe : ProductSafe body)
    (record : RunWitness α → Event) (quiet : ∀ run, added (record run) = []) :
    ProductSafe (receiptObserved body record) :=
  product_bind safe.captureObserved (fun run =>
    product_bind (product_emit (record run) (quiet run)) (fun _ => product_pure run.value))

namespace Deliveries
theorem quiet_state_from_frame (body : WGPrefix Event α) (appends : StateAppends body)
    (frame : StateHistoryFrame delivery? body) : TransmitSecurity.Driver.StateHistorySafe Safe body := by
  intro w a h hi
  obtain ⟨suffix,grown⟩ := appends w a h
  have unchanged := frame w a h
  change (runWGPrefix body w a h).2.filterMap delivery? = h.filterMap delivery? at unchanged
  change (runWGPrefix body w a h).2 = h ++ suffix at grown
  rw [grown,List.filterMap_append] at unchanged
  have empty : suffix.filterMap delivery? = [] :=
    List.append_cancel_left (as := h.filterMap delivery?) (by simpa only [List.append_nil] using unchanged)
  have safe : Safe (h ++ suffix) := hi.quiet (List.filterMap_eq_nil_iff.mp empty)
  change (runPrefix (body.run w) a h).2 = h ++ suffix at grown
  refine ⟨suffix,grown,grown ▸ safe,?_⟩
  cases result : (runPrefix (body.run w) a h).1 <;> first | trivial | exact grown ▸ safe

theorem peer_release (peer : Option PeerId) :
    TransmitSecurity.Driver.StateHistorySafe Safe (CausalJournal.peerRelease peer) :=
  quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) (StagedDisposal.releaseObserved peer)

theorem staged_purge (pid : PeerId) :
    TransmitSecurity.Driver.StateHistorySafe Safe (CausalJournal.stagedPurge pid) :=
  quiet_state Event.stagedDisposal stagedDisposal? (fun _ => rfl) (StagedDisposal.purgeObserved pid)

theorem product_receipt (body : PrefixM Event α) (safe : TransmitSecurity.Driver.ProductHistorySafe Safe body)
    (record : RunWitness α → Event) (quiet : ∀ run, Quiet (record run)) :
    TransmitSecurity.Driver.ProductHistorySafe Safe (receiptObserved body record) :=
  TransmitSecurity.Driver.History.product_bind safe.captureObserved (fun run =>
    TransmitSecurity.Driver.History.product_bind (product_emit (record run) (quiet run))
      (fun _ => TransmitSecurity.Driver.History.product_pure run.value))
end Deliveries

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
