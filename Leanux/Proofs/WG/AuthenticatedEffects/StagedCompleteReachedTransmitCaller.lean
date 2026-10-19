import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitSource

/-! Front outcomes are bound to the actual observed body and returned world.
Normal refusals retain their invocation charge and completed disposal history;
a Stop retains its literal failed source, not an invented error endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier

structure Path (input : Input) (h : List Event) (w : WGWorld) (a : Ambient)
    (value : Except Int PeerId) (v : WGWorld) (b : Ambient) (prior : List Event) : Prop where
  performed : runWGPrefix (body input) w a (inputHistory input h)=(.ok ((value,v),b),prior)

theorem Path.front (path : Path input h w a value v b prior) :
    runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      (.ok ((value,v),b),resultHistory input value w v a b prior) := by
  rw [front_run,path.performed]

theorem Path.continuation (path : Path input h w a value v b prior) :
    runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
      runWGPrefix (tail value) v b (resultHistory input value w v a b prior) := by
  rw [factor]
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have front:=path.front
  change runStatePrefix _ _ _ _=_ at front
  rw [front]
  rfl

theorem Path.accounted (path : Path input h w a value v b prior)
    (before : Accounted h ledger debts locals w) :
    ∃ after, Accounted (resultHistory input value w v a b prior) after debts locals v ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome)∈ledger → (ticket,Status.terminal outcome)∈after :=
  CompleteFront.front_normal input before a b v _ value path.front

/-- The actual completed splice is derived from this observed source run.
Its preceding check/lookup/select states are not extra caller assumptions. -/
theorem Path.native (path : Path input h w a (.ok pid) v b prior) :
    Packets.TxFrontCut input.family input.address input.packets input.mtu w v a b pid := by
  have erased:=HandshakeSecurity.StagedConservation.Front.observed_erases
    Event.transmitInput Event.stagedDisposal stagedDisposal?
    StagedAdmission.Front.routedEvent input w a h
  change (runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h).1=_ at erased
  rw [path.front] at erased
  exact Packets.txFront_cut _ _ _ _ _ _ _ _ _ erased.symm

/-- Even a multi-segment refusal charges this invocation once; any earlier
counted staged disposal remains a separate, already emitted source receipt. -/
theorem Path.refused_once (path : Path input h w a (.error code) v b prior) :
    (code = -EPROTONOSUPPORT ∨ code = -ENOKEY ∨ code = -EDESTADDRREQ ∨ code = -ENOMEM) ∧
    v.dev.map Device.txErrors=(w.dev.map Device.txErrors).map (·+1) ∧
    runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
      (.ok ((code,v),b),resultHistory input (.error code) w v a b prior) := by
  have counted:=StagedAdmission.Front.refused_once input.family input.address input.packets input.mtu
    w v a b h _ code path.front
  refine ⟨counted.1,counted.2,?_⟩
  rw [path.continuation]
  rfl

theorem Path.refused_no_birth (path : Path input h w a (.error code) v b prior)
    (before : Accounted h ledger debts locals w) :
    births (resultHistory input (.error code) w v a b prior)=births h := by
  obtain ⟨history,r,after,position,value,_,_,_,normal⟩:=
    StagedAdmission.Front.normal_result (StagedAdmission.Front.coreEntry before.entry.core) input rfl
      a b v _ (.error code) path.front
  obtain ⟨_,_,_,_,old,snapshot,cut,next⟩:=normal
  have canonical:=cut.canonical (StagedAdmission.Front.Entry.withInput_canonical
    (StagedAdmission.Front.coreEntry before.entry.core) input rfl)
  rw [position,births_emit]
  have quiet : birthPackets (StagedAdmission.Front.routedEvent input r)=[] := by
    simp [StagedAdmission.Front.routedEvent,birthPackets,value]
  rw [quiet,Staged.Origins.freshTickets,List.append_nil,canonical]
  rfl

structure Stopped (input : Input) (h : List Event) (w : WGWorld) (a : Ambient)
    (stop : Stop) (last : List Event) : Prop where
  performed : runWGPrefix (body input) w a (inputHistory input h)=(.error stop,last)

theorem Stopped.whole (path : Stopped input h w a stop last) :
    runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
      (.error stop,last) := by
  rw [factor]
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have front : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      (.error stop,last) := by rw [front_run,path.performed]
  change runStatePrefix _ _ _ _=_ at front
  rw [front]

/-- This is the existing accounting checkpoint beside the literal failed
body, not an additional claim that all silent native states equal it. -/
theorem Stopped.accounted (path : Stopped input h w a stop last)
    (before : Accounted h ledger debts locals w) :
    ∃ after snapshot, StagedAdmission.Front.Checkpoint
      ((StagedAdmission.Front.coreEntry before.entry.core).withInput input) last after snapshot ∧
      Accounted last after debts locals snapshot ∧
      PacketOrigins.snapshot snapshot=PacketOrigins.snapshot w ∧
      StagedAdmission.Front.Ownership.view snapshot=StagedAdmission.Front.Ownership.view w := by
  apply CompleteFront.front_stopped input before a last stop
  rw [front_run,path.performed]

/-- No successful front or staging premise is required. The normal branch
has the same actual returned world and receipt; the other branch has its real Stop. -/
theorem caller_cases (input : Input) (history : List Event) (w : WGWorld) (a : Ambient)
    (before : Accounted history ledger debts locals w) :
    (∃ stop last, Stopped input history w a stop last) ∨
    (∃ value v b prior after, Path input history w a value v b prior ∧
      Accounted (resultHistory input value w v a b prior) after debts locals v) := by
  cases run : runWGPrefix (body input) w a (inputHistory input history) with
  | mk result last=>
    cases result with
    | error stop=>exact Or.inl ⟨stop,last,⟨run⟩⟩
    | ok out=>
      obtain ⟨⟨value,v⟩,b⟩:=out
      have path : Path input history w a value v b last:=⟨run⟩
      obtain ⟨after,accounted,_⟩:=path.accounted before
      exact Or.inr ⟨value,v,b,last,after,path,accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
