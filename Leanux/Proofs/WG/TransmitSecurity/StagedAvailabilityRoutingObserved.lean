import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityDisposalFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableRouting

/-! The original routing receipt uses its actual position after internal
input and disposal observations, including a prefix retained on Stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal HandshakeSecurity.StagedConservation

theorem routing_rich (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (AuthenticatedEffects.CausalJournal.front family addr packets mtu) := by
  unfold AuthenticatedEffects.CausalJournal.front Front.observed
  apply StatePrefixEnsures.bind (state_emit (.transmitInput ⟨family,addr,packets,mtu⟩) rfl)
  intro _
  let body := Front.frontWith (Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu
  let record := fun r => Event.old (Journal.Event.routed family addr packets mtu r)
  change StateSafe (receiptWGObserved body record)
  intro w a h before
  have appends : StateAppends body := Front.front_appends (Front.observedOps_appends _ _) _ _ _ _
  have frame : StateHistoryFrame allocation? body :=
    Front.front_frame (Front.observedOps_frame Event.stagedDisposal stagedDisposal? allocation? (fun _ => rfl)) _ _ _ _
  have erase : ErasesStatePrefix body (Packets.txFront family addr packets mtu) :=
    Front.front_erases (Front.observedOps_erases _ _) _ _ _ _
  obtain ⟨suffix,grown⟩ := appends w a h
  have quiet : ∀ event ∈ suffix, allocation? event = none := suffix_quiet frame grown
  have safe := before.2.quiet quiet
  have inv := before.1.append (fun _ event member => no_use (quiet event member))
  have equation := runWGPrefix_receiptWGObserved body record w a h
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : runWGPrefix body w a h with
  | mk result history =>
    simp only [runWGPrefix,runStatePrefix] at run
    rw [run] at grown ⊢
    dsimp only at grown
    subst history
    cases result with
    | error stop => exact ⟨suffix,rfl,safe,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      have native : ((Packets.txFront family addr packets mtu).run w).run a = .ok ((value,v),b) :=
        (erase w a h).symm.trans (congrArg Prod.fst run)
      let receipt : Journal.RoutingHistory.Receipt := ⟨family,addr,packets,mtu,⟨value,w,v,a,b⟩⟩
      have emitted := safe.emit (event := record receipt.run) True.intro
      refine ⟨suffix ++ [record receipt.run],?_,?_,?_,?_⟩
      · exact List.append_assoc _ _ _
      · exact emitted
      · cases value with
        | error err =>
          have kept := (routing_failure receipt native err rfl inv).append (quiet_singleton (event := record receipt.run) rfl)
          exact kept
        | ok pid =>
          have kept := routing_success receipt native pid rfl inv
          exact kept
      · exact emitted

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
