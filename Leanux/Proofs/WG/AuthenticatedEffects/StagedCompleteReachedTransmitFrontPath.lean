import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontFrames

/-! Connected normal native guards identify the actual entry to each front
residual. The stopped classification retains a literal failed native action
at its own returned-prefix world, never an existential checkpoint world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier Lifetimes
set_option maxHeartbeats 600000

def Selected (input : Input) (h : List Event) (w : WGWorld) (a : Ambient)
    (decision : Choice) (v : WGWorld) (b : Ambient) : Prop :=
  ∃ u c peer q d,
    ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.ok ((true,u),c) ∧
    ((lookupDst input.family input.address).run u).run c=.ok ((peer,q),d) ∧
    runWGPrefix (choose input peer) q d h=(.ok ((decision,v),b),h)

theorem Selected.accounted (path : Selected input h w a decision v b)
    (before : Accounted h ledger debts locals w) : Accounted h ledger debts locals v := by
  obtain ⟨u,c,peer,q,d,checked,looked,selected⟩:=path
  exact (choose_account input peer (lookup_account input (check_account input before checked) looked) selected).2

theorem decision_run (input : Input) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (decisionPrefix input) w a h=
      match ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((false,v),b) => (.ok ((.error (-EPROTONOSUPPORT),v),b),h)
      | .ok ((true,u),c) =>
        match ((lookupDst input.family input.address).run u).run c with
        | .error stop => (.error stop,h)
        | .ok ((peer,q),d) =>
          let selected:=runWGPrefix (choose input peer) q d h
          (selected.1.map (fun ((value,v),b)=>((.ok value,v),b)),selected.2) := by
  simp only [runWGPrefix,decisionPrefix,liftWGPrefix,runStatePrefix_bind,runStatePrefix_lift]
  cases first : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨accepted,u⟩,c⟩:=out
    cases accepted with
    | false => rfl
    | true =>
      simp only [Bool.not_true,Bool.false_eq_true,ite_false,runStatePrefix_bind,runStatePrefix_lift]
      cases lookup : ((lookupDst input.family input.address).run u).run c with
      | error stop => rfl
      | ok out =>
        obtain ⟨⟨peer,q⟩,d⟩:=out
        dsimp only
        cases selected : runStatePrefix (choose input peer) q d h with
        | mk result last =>
          cases result with
          | error stop => rfl
          | ok out => obtain ⟨⟨value,v⟩,b⟩:=out; rfl

theorem Selected.literal (path : Selected input h w a decision v b) :
    runWGPrefix (decisionPrefix input) w a h=(.ok ((.ok decision,v),b),h) := by
  obtain ⟨u,c,peer,q,d,checked,looked,selected⟩:=path
  simp only [decision_run,checked,looked,selected,Except.map]

theorem Selected.continuation (path : Selected input h w a decision v b) :
    runWGPrefix (body input) w a h=runWGPrefix (resolve input decision) v b h := by
  rw [body_factor]
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have run:=path.literal
  change runStatePrefix _ _ _ _=_ at run
  rw [run]
  rfl

inductive PrefixFailure (input : Input) (h : List Event) (w : WGWorld) (a : Ambient) (stop : Stop) : Prop where
  | check (failed : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.error stop)
  | lookup (u : WGWorld) (c : Ambient)
      (checked : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.ok ((true,u),c))
      (failed : ((lookupDst input.family input.address).run u).run c=.error stop)
  | choose (u q : WGWorld) (c d : Ambient) (peer : Option PeerId)
      (checked : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.ok ((true,u),c))
      (looked : ((lookupDst input.family input.address).run u).run c=.ok ((peer,q),d))
      (failed : runWGPrefix (Front.choose input peer) q d h=(.error stop,h))

theorem PrefixFailure.literal (path : PrefixFailure input h w a stop) :
    runWGPrefix (decisionPrefix input) w a h=(.error stop,h) := by
  cases path with
  | check failed => rw [decision_run,failed]
  | lookup u c checked failed => simp only [decision_run,checked,failed]
  | choose u q c d peer checked looked failed => simp only [decision_run,checked,looked,failed,Except.map]

/-- A selected failure has the same concrete guard entry. Earlier native
subcuts are retained in the constructor, even though no failed world returns. -/
theorem PrefixFailure.accounted_cut (path : PrefixFailure input h w a stop)
    (before : Accounted h ledger debts locals w) :
    (∃ u c, Accounted h ledger debts locals u ∧
      ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.ok ((true,u),c) ∧
      ((lookupDst input.family input.address).run u).run c=.error stop) ∨
    (∃ u q c d peer, Accounted h ledger debts locals q ∧
      ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.ok ((true,u),c) ∧
      ((lookupDst input.family input.address).run u).run c=.ok ((peer,q),d) ∧
      runWGPrefix (Front.choose input peer) q d h=(.error stop,h)) ∨
    ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=.error stop := by
  cases path with
  | check failed => exact Or.inr (Or.inr failed)
  | lookup u c checked failed => exact Or.inl ⟨u,c,check_account input before checked,checked,failed⟩
  | choose u q c d peer checked looked failed =>
    exact Or.inr (Or.inl ⟨u,q,c,d,peer,lookup_account input (check_account input before checked) looked,checked,looked,failed⟩)

/-- Exhaustive source decomposition. A returned false check is an invocation
refusal, while failed checks/lookup/selection retain their actual failed run. -/
theorem decision_cases (input : Input) (w : WGWorld) (a : Ambient) (h : List Event) :
    (∃ stop, PrefixFailure input h w a stop) ∨
    (∃ v b, ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a=
      .ok ((false,v),b) ∧ runWGPrefix (decisionPrefix input) w a h=(.ok ((.error (-EPROTONOSUPPORT),v),b),h)) ∨
    (∃ decision v b, Selected input h w a decision v b) := by
  cases checked : ((Packets.txCheck input.family input.address input.packets input.mtu).run w).run a with
  | error stop => exact Or.inl ⟨stop,.check checked⟩
  | ok out =>
    obtain ⟨⟨accepted,u⟩,c⟩:=out
    cases accepted with
    | false => exact Or.inr (Or.inl ⟨u,c,rfl,by rw [decision_run,checked]⟩)
    | true =>
      cases looked : ((lookupDst input.family input.address).run u).run c with
      | error stop => exact Or.inl ⟨stop,.lookup u c checked looked⟩
      | ok out =>
        obtain ⟨⟨peer,q⟩,d⟩:=out
        cases selected : runWGPrefix (choose input peer) q d h with
        | mk result last =>
          have history:=choose_history input peer q d h
          rw [selected] at history
          change last=h at history
          subst last
          cases result with
          | error stop => exact Or.inl ⟨stop,.choose u q c d peer checked looked selected⟩
          | ok out =>
            obtain ⟨⟨decision,v⟩,b⟩:=out
            exact Or.inr (Or.inr ⟨decision,v,b,⟨u,c,peer,q,d,checked,looked,selected⟩⟩)

/-- The actual input marker is part of this literal guard prefix. -/
theorem Selected.input_literal
    (path : Selected input (inputHistory input h) w a decision v b) :
    runWGPrefix (do emitStatePrefix (.transmitInput input); decisionPrefix input) w a h=
      (.ok ((.ok decision,v),b),inputHistory input h) := by
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind,runStatePrefix_emit]
  exact path.literal

/-- A failed front is either a failed fixed guard prefix, or its actual
resolved callback fails from the concretely accounted selection cut. The
latter keeps overflow/release/splice internal correspondence as a separate
source obligation; it is not replaced by a checkpoint's existential world. -/
theorem stopped_classify (before : Accounted h ledger debts locals w)
    (stopped : Transmit.Stopped input h w a stop last) :
    (PrefixFailure input (inputHistory input h) w a stop ∧ last=inputHistory input h) ∨
    (∃ decision v b, Selected input (inputHistory input h) w a decision v b ∧
      Accounted (inputHistory input h) ledger debts locals v ∧
      runWGPrefix (resolve input decision) v b (inputHistory input h)=(.error stop,last)) := by
  have marked : Accounted (inputHistory input h) ledger debts locals w :=
    before.append_quiet [.transmitInput input]
      (by intro event member; cases List.mem_singleton.mp member; rfl)
      (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  rcases decision_cases input w a (inputHistory input h) with failed | refused | selected
  · obtain ⟨reason,path⟩:=failed
    have result:=stopped.performed
    rw [body_factor] at result
    change runStatePrefix (_ >>= _) w a (inputHistory input h)=_ at result
    rw [runStatePrefix_bind] at result
    have literal:=path.literal
    change runStatePrefix _ _ _ _=_ at literal
    rw [literal] at result
    have equal : reason=stop ∧ inputHistory input h=last := by simpa only [Prod.mk.injEq,Except.error.injEq] using result
    obtain ⟨rfl,rfl⟩:=equal
    exact Or.inl ⟨path,rfl⟩
  · obtain ⟨v,b,_,literal⟩:=refused
    have result:=stopped.performed
    rw [body_factor] at result
    change runStatePrefix (_ >>= _) w a (inputHistory input h)=_ at result
    rw [runStatePrefix_bind] at result
    change runStatePrefix _ _ _ _=_ at literal
    rw [literal] at result
    cases result
  · obtain ⟨decision,v,b,path⟩:=selected
    exact Or.inr ⟨decision,v,b,path,path.accounted marked,path.continuation.symm.trans stopped.performed⟩

/-- These are the concrete residuals identified by the selection path. -/
theorem resolve_release (input : Input) (peer : Option PeerId) (code : Int) :
    resolve input (.release peer code) = (do
      StagedAdmission.Front.ops.put peer
      let err ← liftWGPrefix (Packets.txError input.family (input.packets.head?.getD {bytes := []}) code)
      pure (.error err)) := by
  simp only [resolve,selectedWith,bind_assoc,pure_bind,afterSelected]
  rfl

theorem resolve_splice (input : Input) (pid : PeerId) (packets : List Packet) :
    resolve input (.splice pid packets) = (do
      StagedAdmission.Front.ops.trim pid
      liftWGPrefix (xmitSplice pid packets)
      pure (.ok pid)) := by
  simp only [resolve,selectedWith,bind_assoc,pure_bind,afterSelected]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front
