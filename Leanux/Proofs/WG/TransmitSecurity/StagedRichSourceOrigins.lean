import Leanux.Proofs.WG.TransmitSecurity.StagedAllocationOrigins

/-! Rich input/disposal cuts retain the original staged-origin claim at the
actual outer routing receipt position. Its native body may append observations
before returning; those positions are never silently identified with entry. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
open HandshakeSecurity.StagedConservation

theorem quiet_history {action : WGPrefix Event α}
    (appends : StateAppends action) (quiet : StateHistoryFrame selection? action) :
    Driver.StateHistorySafe Safe action := by
  intro w a h before
  obtain ⟨suffix,position⟩ := appends w a h
  have noSelection : suffix.filterMap selection? = [] := by
    have frame := quiet w a h
    rw [position,List.filterMap_append] at frame
    have lengths := congrArg List.length frame
    cases found : suffix.filterMap selection? with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at lengths; omega
  have safe : Safe (runPrefix (action.run w) a h).2 := by
    rw [position]
    apply before.quiet
    intro event member
    apply (quiet_iff event).mpr
    cases found : selection? event with
    | none => rfl
    | some value =>
      have present := List.mem_filterMap.mpr ⟨event,member,found⟩
      rw [noSelection] at present
      cases present
  refine ⟨suffix,position,safe,?_⟩
  cases (runPrefix (action.run w) a h).1
  · trivial
  · exact safe

theorem disposal_release_history (peer : Option PeerId) :
    Driver.StateHistorySafe Safe (peerRelease peer) :=
  quiet_history (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run w))

theorem disposal_release_observed (peer : Option PeerId) : StateSafe (peerRelease peer) :=
  state_quiet (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl)
      ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run w))
    (focusStatePrefix_erases _ _ (HandshakeSecurity.StagedDisposal.release_erases peer))
    (fun _ => Native.peer_put peer)

theorem rich_routing_receipt (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (receiptWGObserved
      (Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu)
      (fun run => Event.old (.routed family addr packets mtu run))) := by
  let body := Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu
  have history := quiet_history
    (Front.front_appends (Front.observedOps_appends Event.stagedDisposal stagedDisposal?) family addr packets mtu)
    (Front.front_frame (Front.observedOps_frame Event.stagedDisposal stagedDisposal? selection? (fun _ => rfl))
      family addr packets mtu)
  have erased := Front.front_erases (Front.observedOps_erases Event.stagedDisposal stagedDisposal?) family addr packets mtu
  intro w a h before
  obtain ⟨suffix,position,safe,_⟩ := history w a h before.2
  change (runWGPrefix body w a h).2 = h ++ suffix at position
  change Safe (runWGPrefix body w a h).2 at safe
  have equation := runWGPrefix_receiptWGObserved body
    (fun run => Event.old (.routed family addr packets mtu run)) w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : runWGPrefix body w a h with
  | mk result tail =>
    rw [run] at position safe
    simp only [runWGPrefix,runStatePrefix] at run
    rw [run]
    cases result with
    | error stop => exact ⟨suffix,position,safe,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      change tail = h ++ suffix at position
      change Safe tail at safe
      have native : ((Packets.txFront family addr packets mtu).run w).run a = .ok ((value,v),b) :=
        (erased w a h).symm.trans (congrArg Prod.fst run)
      let receipt : Journal.RoutingHistory.Receipt := ⟨family,addr,packets,mtu,⟨value,w,v,a,b⟩⟩
      have inv : Inv tail w := by rw [position]; exact before.1.append suffix
      have next : Safe (tail ++ [.old (.routed family addr packets mtu receipt.run)]) := safe.emit True.intro
      refine ⟨suffix ++ [.old (.routed family addr packets mtu receipt.run)],?_,next,?_,next⟩
      · change tail ++ [_] = h ++ (suffix ++ [_])
        rw [position,List.append_assoc]
      · cases value with
        | error err => exact (routing_failure receipt native err rfl inv).append _
        | ok pid => exact routing_success receipt native pid rfl inv

theorem rich_routing_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (front family addr packets mtu) := by
  unfold front Front.observed
  exact StatePrefixEnsures.bind (state_emit _ True.intro)
    (fun _ => rich_routing_receipt family addr packets mtu)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
