import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalReceipts

/-! The enriched front's real callbacks retain their last counted checkpoint
on Stop. Native source equations connect the entry to each emitted receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

abbrev ops : HandshakeSecurity.StagedConservation.Front.Ops (WGPrefix Event) := HandshakeSecurity.StagedConservation.Front.observedOps
  Event.stagedDisposal stagedDisposal?

def Idle (entry : Entry) (history : List Event) (w : WGWorld) (_a : Ambient) : Prop :=
  history = entry.history ∧ QueueInv history entry.ledger w

theorem Idle.carry (before : Idle entry history w a) : Carry entry history w a := by
  obtain ⟨rfl,queues⟩ := before
  exact ⟨entry.ledger,entry.world,.initial,queues⟩

theorem idle_native {action : WG.M α}
    (frame : ∀ history ledger, Preserves (QueueInv history ledger) action) :
    StatePrefixPreserves (Idle entry) (Safe entry) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift
  · intro history w a before
    exact before.carry.safe
  · intro history w a value v b before run
    exact ⟨before.1,(hoare_iff_run_ambient _ _ _).mp
      (frame history entry.ledger) w a value v b before.2 run⟩

theorem trim_run (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (ops.trim pid) w a h =
      match ((Lifetimes.xmitTrim pid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((value,v),b) =>
        (.ok ((value,v),b),h ++ [.stagedDisposal (.overflow pid ⟨value,w,v,a,b⟩)]) := by
  change runPrefix (focusPrefix Event.stagedDisposal stagedDisposal?
    ((HandshakeSecurity.StagedDisposal.overflowObserved pid).run w)) a h = _
  cases native : ((Lifetimes.xmitTrim pid).run w).run a with
  | error stop =>
    have localRun : runWGPrefix (HandshakeSecurity.StagedDisposal.overflowObserved pid)
        w a (h.filterMap stagedDisposal?) = (.error stop,h.filterMap stagedDisposal? ++ []) := by
      rw [HandshakeSecurity.StagedDisposal.overflowObserved,runWGPrefix_receiptWGObserved,
        runWGPrefix_lift,native]
      simp
    simpa only [List.map_nil,List.append_nil] using
      (focusPrefix_suffix Event.stagedDisposal stagedDisposal?
        ((HandshakeSecurity.StagedDisposal.overflowObserved pid).run w) a h _ [] localRun)
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have localRun : runWGPrefix (HandshakeSecurity.StagedDisposal.overflowObserved pid)
        w a (h.filterMap stagedDisposal?) =
        (.ok ((value,v),b),h.filterMap stagedDisposal? ++ [.overflow pid ⟨value,w,v,a,b⟩]) := by
      rw [HandshakeSecurity.StagedDisposal.overflowObserved,runWGPrefix_receiptWGObserved,
        runWGPrefix_lift,native]
    exact focusPrefix_suffix Event.stagedDisposal stagedDisposal? _ a h _ [_] localRun

theorem trim_checked (pid : PeerId) :
    StatePrefixEnsures (Idle entry) (Safe entry) (ops.trim pid) (fun _ => Carry entry) := by
  intro w a h before
  have equation := trim_run pid w a h
  change runPrefix ((ops.trim pid).run w) a h = _ at equation
  rw [equation]
  cases native : ((Lifetimes.xmitTrim pid).run w).run a with
  | error stop => exact ⟨[],by simp,before.carry.safe,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : WGRunWitness Unit := ⟨value,w,v,a,b⟩
    obtain ⟨partition⟩ := HandshakeSecurity.StagedDisposal.overflow_exact pid r native
    have existsDevice : ∃ d, w.dev = some d := by
      cases device : w.dev with
      | none =>
        have impossible := partition.before
        simp [Staged.stagedAt,r,device] at impossible
      | some d => exact ⟨d,rfl⟩
    obtain ⟨d,device⟩ := existsDevice
    have epoch : Packets.epoch w = some d.ifindex := by simp [Packets.epoch,device]
    obtain ⟨rfl,queues⟩ := before
    have cut := Checkpoint.trimmed (entry := entry) pid r native partition d.ifindex epoch queues
    obtain ⟨_,_,_,after⟩ := cut.accounted
    exact ⟨[.stagedDisposal (.overflow pid r)],rfl,⟨_,_,cut⟩,⟨_,_,cut,after⟩⟩

theorem put_run (peer : Option PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (ops.put peer) w a h =
      match ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((result,v),b) =>
        let hist := h ++ [.stagedDisposal (.release peer ⟨result,w,v,a,b⟩)]
        match result with
        | none => (.ok (((),v),b),hist)
        | some (pid,p) => (((HandshakeSecurity.StagedDisposal.releaseFinish pid p).run v).run b,hist) := by
  change runPrefix (focusPrefix Event.stagedDisposal stagedDisposal?
    ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run w)) a h = _
  cases native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a with
  | error stop =>
    have localRun : runWGPrefix (HandshakeSecurity.StagedDisposal.releaseObserved peer)
        w a (h.filterMap stagedDisposal?) = (.error stop,h.filterMap stagedDisposal? ++ []) := by
      rw [HandshakeSecurity.StagedDisposal.release_run,native]
      simp
    simpa only [List.map_nil,List.append_nil] using
      (focusPrefix_suffix Event.stagedDisposal stagedDisposal?
        ((HandshakeSecurity.StagedDisposal.releaseObserved peer).run w) a h _ [] localRun)
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    have localRun := HandshakeSecurity.StagedDisposal.release_run peer w a (h.filterMap stagedDisposal?)
    rw [native] at localRun
    cases result with
    | none => exact focusPrefix_suffix Event.stagedDisposal stagedDisposal? _ a h _ [_] localRun
    | some pair =>
      rcases pair with ⟨pid,p⟩
      exact focusPrefix_suffix Event.stagedDisposal stagedDisposal? _ a h _ [_] localRun

theorem put_checked (peer : Option PeerId) :
    StatePrefixEnsures (Idle entry) (Safe entry) (ops.put peer) (fun _ => Carry entry) := by
  intro w a h before
  have equation := put_run peer w a h
  change runPrefix ((ops.put peer).run w) a h = _ at equation
  rw [equation]
  cases native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a with
  | error stop => exact ⟨[],by simp,before.carry.safe,True.intro⟩
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    obtain ⟨rfl,queues⟩ := before
    cases result with
    | none =>
      let r : WGRunWitness (Option (PeerId × Peer)) := ⟨none,w,v,a,b⟩
      obtain ⟨epoch,staged⟩ := Native.release_none peer r native rfl
      have after := queues.views epoch staged
      have cut := Checkpoint.nonfinal (entry := entry) peer r native rfl after
      exact ⟨[.stagedDisposal (.release peer r)],rfl,⟨_,_,cut⟩,
        ⟨_,_,cut,after.append_history _⟩⟩
    | some pair =>
      rcases pair with ⟨pid,p⟩
      let r : WGRunWitness (Option (PeerId × Peer)) := ⟨some (pid,p),w,v,a,b⟩
      obtain ⟨d,_,device,_,_,_⟩ := HandshakeSecurity.StagedDisposal.release_exact peer r native pid p rfl
      change w.dev = some d at device
      have epoch : Packets.epoch w = some d.ifindex := by simp [Packets.epoch,device]
      have cut := Checkpoint.released (entry := entry) peer r native pid p rfl d.ifindex epoch queues
      have after := cut.accounted.2.2.2
      refine ⟨[.stagedDisposal (.release peer r)],rfl,⟨_,_,cut⟩,?_⟩
      dsimp only
      cases finish : ((HandshakeSecurity.StagedDisposal.releaseFinish pid p).run v).run b with
      | error stop => trivial
      | ok out =>
        rcases out with ⟨⟨value,final⟩,clock⟩
        exact ⟨_,_,cut,(hoare_iff_run_ambient _ _ _).mp (Native.release_finish pid p)
          v b value final clock after finish⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
