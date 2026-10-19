import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldChecked
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldNativeFrames

/-! Source composition from the actual take through key borrowing and the
checked nonce loop. The same ledger and active selected frontier survive Stop;
the exact no-key and allocation callbacks remain explicit local obligations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal HeldFrontier
open HandshakeSecurity.StagedConservation

def noKey (pid : PeerId) (peer : Peer) (key : Option KeypairId) (invalid : Bool) : WGPrefix Event Unit :=
  Restore.noKeyWith effects stagedRestore (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease)
    pid peer.staged key invalid

def submit (pid : PeerId) (kid : KeypairId) (packets : List DataPacket) : WGPrefix Event Unit := do
  let owner ← liftWGPrefix (IndexOwner.peerDeref (.keypair kid))
  liftWGPrefix (peerGet owner)
  let items ← state (Journal.allocate packets)
  CausalJournal.create pid items

theorem staging_factor (pid : PeerId) : Driver.stagingObserved hooks pid = (do
    let choice ← CausalJournal.selection pid
    match choice with
    | none => pure ()
    | some (peer,keypair) =>
      RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
        (noKey pid peer) (submit pid) pid peer keypair) := by
  unfold Driver.stagingObserved
  congr 1
  funext choice
  cases choice with
  | none => rfl
  | some pair =>
    obtain ⟨peer,keypair⟩ := pair
    cases keypair <;> rfl

/-- This actual native take initializes the fixed selected ledger. Borrowing
and nonce checks retain a concrete active frontier on Stop. The same exact
ordered batch reaches the submission callback; no old successful selection
receipt or containing-call success is assumed. -/
theorem after_take (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Core history ledger debts r.run.before)
    (Safe : List Event → Prop) (Post : List Event → WGWorld → Ambient → Prop)
    (postSafe : ∀ h w a, Post h w a → Safe h) :
    ∃ after generation, Step ledger after ∧
      ((∀ h, Anchor after debts generation r.pid peer history.length h → Safe h) →
      (∀ kp invalid, StatePrefixEnsures
        (Held after debts generation r.pid peer history.length) Safe (noKey r.pid peer kp invalid) (fun _ => Post)) →
      (∀ kid packets, StatePrefixEnsures
        (fun h w a => Held after debts generation r.pid peer history.length h w a ∧
          BatchPayload.Shape r.pid kid peer.staged packets) Safe (submit r.pid kid packets) (fun _ => Post)) →
      let out := runWGPrefix (Driver.stagingObserved hooks r.pid) r.run.before r.run.ambientBefore history
      ∃ suffix, out.2 = (history ++ [.stagingTaken r]) ++ suffix ∧ Safe out.2 ∧
        match out.1 with
        | .error _ => True
        | .ok ((_,w),a) => Post out.2 w a) := by
  obtain ⟨after,generation,step,held⟩ := taken r native chosen before
  refine ⟨after,generation,step,?_⟩
  intro frontier rejected submitted
  have takeRun : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
      .ok ((some peer,r.run.after),r.run.ambientAfter) := by rw [←chosen]; exact native
  have sameReceipt : (⟨r.pid,⟨some peer,r.run.before,r.run.after,r.run.ambientBefore,r.run.ambientAfter⟩⟩ : Take.Receipt) = r := by
    cases r with
    | mk pid witness => cases witness; cases chosen; rfl
  have selectionRun := runWGPrefix_receiptWGObserved (Take.observed Event.stagingTaken r.pid)
    (fun run => Event.old (.responder (.selected r.pid run))) r.run.before r.run.ambientBefore history
  rw [Take.observed_after_take Event.stagingTaken r.pid _ _ _ _ _ (some peer) takeRun,sameReceipt,
    runWGPrefix_lift] at selectionRun
  change runWGPrefix (CausalJournal.selection r.pid) _ _ _ = _ at selectionRun
  rw [staging_factor]
  simp only [runWGPrefix,runStatePrefix_bind]
  change runStatePrefix (CausalJournal.selection r.pid) _ _ _ = _ at selectionRun
  rw [selectionRun]
  cases borrowRun : ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter with
  | error stop => exact ⟨[],by simp,frontier _ held.anchor,True.intro⟩
  | ok out =>
    obtain ⟨⟨choice,v⟩,b⟩ := out
    have borrowed := borrow_held after debts generation r.pid peer history.length Safe frontier
      r.run.after r.run.ambientAfter (history ++ [.stagingTaken r]) held
    obtain ⟨_,_,_,reached⟩ := borrowed
    have lifted := runWGPrefix_lift (Take.borrow (some peer))
      r.run.after r.run.ambientAfter (history ++ [.stagingTaken r])
    change runPrefix ((liftWGPrefix (Take.borrow (some peer))).run r.run.after)
      r.run.ambientAfter (history ++ [.stagingTaken r]) = _ at lifted
    rw [lifted,borrowRun] at reached
    obtain ⟨kid,rfl,afterBorrow⟩ := reached
    let event := Event.old (.responder (.selected r.pid
      ⟨some (peer,kid),r.run.before,v,r.run.ambientBefore,b⟩))
    have afterEvent : Held after debts generation r.pid peer history.length
        ((history ++ [.stagingTaken r]) ++ [event]) v b :=
      afterBorrow.views_append [event] (by intro e member; have same := List.mem_singleton.mp member; subst e; rfl)
        rfl rfl rfl
    have checked := HeldChecked.checked after debts generation r.pid peer history.length kid Safe frontier
      Post postSafe (noKey r.pid peer) (submit r.pid) rejected submitted
    obtain ⟨suffix,extended,safe,post⟩ := checked v b ((history ++ [.stagingTaken r]) ++ [event]) afterEvent
    refine ⟨[event] ++ suffix,?_,safe,?_⟩
    · simpa only [runStatePrefix,event,List.append_assoc] using extended
    · have unpack (out : Except Stop ((Unit × WGWorld) × Ambient)) (h : List Event) :
          (match out with
            | .error _ => True
            | .ok (value,a) => Post h value.2 a) →
          (match out with
            | .error _ => True
            | .ok ((_,w),a) => Post h w a) := by
        cases out with
        | error _ => exact id
        | ok pair => obtain ⟨⟨_,w⟩,a⟩ := pair; exact id
      let actual := runWGPrefix
        (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
          (noKey r.pid peer) (submit r.pid) r.pid peer kid)
        v b ((history ++ [.stagingTaken r]) ++ [event])
      have normalized := unpack actual.1 actual.2 (by
        cases result : actual.1 with
        | error stop => trivial
        | ok pair =>
          obtain ⟨⟨value,w⟩,a⟩ := pair
          have result' := result
          dsimp only [actual,runWGPrefix,runStatePrefix] at result'
          rw [result'] at post
          exact post)
      simpa only [actual,runWGPrefix,runStatePrefix,event] using normalized

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldSource
