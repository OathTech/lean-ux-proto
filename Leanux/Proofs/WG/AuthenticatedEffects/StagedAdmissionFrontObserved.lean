import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontReceipt

/-! The full enriched front admits tickets only at its actual routed receipt.
A stopped front retains the actual entry or last completed disposal checkpoint.
The canonical ticket domain and earlier terminal records remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

def Entry.withInput (entry : Entry) (input : Input) : Entry where
  history := entry.history ++ [.transmitInput input]
  births := entry.births
  ledger := entry.ledger
  world := entry.world
  valid := entry.valid
  bounded := bounded_mono entry.bounded (by simp)
  queues := entry.queues.append_history _

theorem Entry.withInput_canonical (entry : Entry) (input : Input)
    (canonical : entry.births = Staged.Obligations.births entry.history) :
    (entry.withInput input).births = Staged.Obligations.births (entry.withInput input).history := by
  exact canonical.trans (births_quiet _ rfl).symm

def Finished (entry : Entry) (input : Input) (history : List Event) : Prop :=
  Safe entry history ∨ ∃ priorHistory r ledger,
    history = priorHistory ++ [routedEvent input r] ∧ Normal entry input r priorHistory ledger

def Result (entry : Entry) (input : Input) (value : Except Int PeerId)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ priorHistory r ledger, history = priorHistory ++ [routedEvent input r] ∧
    r.value = value ∧ r.before = entry.world ∧ r.after = w ∧ r.ambientAfter = a ∧ Normal entry input r priorHistory ledger

theorem front_run (input : Input) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h =
      match runWGPrefix (body input.family input.address input.packets input.mtu)
        w a (h ++ [.transmitInput input]) with
      | (.error stop,hist) => (.error stop,hist)
      | (.ok ((value,v),b),hist) =>
        (.ok ((value,v),b),hist ++ [routedEvent input ⟨value,w,v,a,b⟩]) := by
  change runStatePrefix
    (emitStatePrefix (.transmitInput input) >>= fun _ =>
      receiptWGObserved (body input.family input.address input.packets input.mtu) (routedEvent input)) w a h = _
  rw [runStatePrefix_bind,runStatePrefix_emit]
  dsimp only
  have rule := runWGPrefix_receiptWGObserved
    (body input.family input.address input.packets input.mtu) (routedEvent input)
    w a (h ++ [.transmitInput input])
  change runStatePrefix
    (receiptWGObserved (body input.family input.address input.packets input.mtu) (routedEvent input))
    w a (h ++ [.transmitInput input]) = _ at rule
  rw [rule]
  cases executed : runWGPrefix (body input.family input.address input.packets input.mtu)
      w a (h ++ [.transmitInput input]) with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out => rcases out with ⟨⟨value,v⟩,b⟩; rfl


/-- The complete final callback derives its splice ledger and canonical births
from the actual observed run. Stop retains a nontrivial accounted checkpoint. -/
theorem front_checked (entry : Entry) (input : Input)
    (canonical : entry.births = Staged.Obligations.births entry.history) :
    StatePrefixEnsures (fun h w _ => h = entry.history ∧ w = entry.world)
      (Finished (entry.withInput input) input)
      (CausalJournal.front input.family input.address input.packets input.mtu)
      (Result (entry.withInput input) input) := by
  intro w a h before
  obtain ⟨rfl,rfl⟩ := before
  let initial := entry.withInput input
  obtain ⟨suffix,append,safe,normal⟩ := body_checked (entry := initial)
    input.family input.address input.packets input.mtu entry.world a initial.history ⟨rfl,initial.queues⟩
  have equation := front_run input entry.world a entry.history
  change runPrefix
    ((CausalJournal.front input.family input.address input.packets input.mtu).run entry.world) a entry.history = _ at equation
  rw [equation]
  cases executed : runWGPrefix (body input.family input.address input.packets input.mtu)
      entry.world a initial.history with
  | mk out hist =>
    change runPrefix ((body input.family input.address input.packets input.mtu).run entry.world)
      a initial.history = _ at executed
    rw [executed] at append safe normal
    change runWGPrefix (body input.family input.address input.packets input.mtu)
      entry.world a (entry.history ++ [.transmitInput input]) = _ at executed
    rw [executed]
    cases out with
    | error stop =>
      dsimp only [Finished,Result]
      refine ⟨[.transmitInput input] ++ suffix,?_,Or.inl safe,True.intro⟩
      simpa only [initial,Entry.withInput,List.append_assoc] using append
    | ok value =>
      rcases value with ⟨⟨result,v⟩,b⟩
      let r : WGRunWitness (Except Int PeerId) := ⟨result,entry.world,v,a,b⟩
      have native := HandshakeSecurity.StagedConservation.Front.front_erases
        (HandshakeSecurity.StagedConservation.Front.observedOps_erases Event.stagedDisposal stagedDisposal?)
        input.family input.address input.packets input.mtu entry.world a initial.history
      change (runWGPrefix (body input.family input.address input.packets input.mtu)
        entry.world a (entry.history ++ [.transmitInput input])).1 = _ at native
      rw [executed] at native
      obtain ⟨ledger,checked⟩ := completed input r native.symm (entry.withInput_canonical input canonical) normal
      dsimp only [Finished,Result]
      refine ⟨[.transmitInput input] ++ suffix ++ [routedEvent input r],?_,?_,?_⟩
      · change hist = initial.history ++ suffix at append
        rw [append]
        simp only [initial,Entry.withInput,List.append_assoc,r]
      · exact Or.inr ⟨hist,r,ledger,rfl,checked⟩
      · exact ⟨hist,r,ledger,rfl,rfl,rfl,rfl,rfl,checked⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
