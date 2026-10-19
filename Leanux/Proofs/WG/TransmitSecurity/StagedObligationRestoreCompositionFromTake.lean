import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreComposition

/-! A take-position seed for the actual selection/borrow/checked source. The
completed take remains in history on a later Stop, with its selected ledger
already fixed at that cut; a normal restore moves those same tickets back to
its queue. The continued error branch asserts no final ownership frontier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal HandshakeSecurity.StagedConservation

def staging (takeRecord : Take.Receipt → Event)
    (selectedRecord : PeerId → WGRunWitness (Option (Peer × Option KeypairId)) → Event)
    (restoreRecord : Restore.Receipt → Event)
    (o : AuthenticatedEffects.TimerEffects.Ops (WGPrefix Event))
    (queue : PeerId → Bool → WGPrefix Event Unit)
    (submit : PeerId → KeypairId → List DataPacket → WGPrefix Event Unit) (pid : PeerId) : WGPrefix Event Unit := do
  let selected ← Take.selection takeRecord selectedRecord pid
  match selected with
  | none => pure ()
  | some (peer,keypair) =>
    RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
      (fun kp invalid => Restore.noKeyWith o (Restore.observed restoreRecord) queue pid peer.staged kp invalid)
      (submit pid) pid peer keypair

/-- The selected location is the actual take event's position. The original
take produces this ledger before borrowing, including when borrowing stops.
The checked source uses actual nonce/selection/restore observations. Its later
queueing and submission contracts remain explicit, local transfer obligations. -/
theorem from_take (takeRecord : Take.Receipt → Event)
    (selectedRecord : PeerId → WGRunWitness (Option (Peer × Option KeypairId)) → Event)
    (restoreRecord : Restore.Receipt → Event) (r : Take.Receipt) (run : r.Valid)
    (peer : Peer) (chosen : r.run.value = some peer) (valid : Valid births ledger)
    (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (unused : pendingAt (.selected history.length) ledger = [])
    (o : AuthenticatedEffects.TimerEffects.Ops (WGPrefix Event))
    (native : ∀ {α} (action : WG.M α), o.step action = liftWGPrefix action)
    (queue : PeerId → Bool → WGPrefix Event Unit)
    (submit : PeerId → KeypairId → List DataPacket → WGPrefix Event Unit)
    (Post : List Event → WGWorld → Ambient → Prop) :
    let source := Pending.staged generation r.pid peer.internalId
    let selected := transferLocation source (.selected history.length) ledger
    StatePrefixEnsures (Restored births selected generation r.pid peer history.length) (fun _ => True)
      (queue r.pid false) (fun _ => Post) →
    (∀ kid packets, StatePrefixEnsures (Held selected generation r.pid peer history.length) (fun _ => True)
      (submit r.pid kid packets) (fun _ => Post)) →
    let out := runWGPrefix (staging takeRecord selectedRecord restoreRecord o queue submit r.pid)
      r.run.before r.run.ambientBefore history
    Step ledger selected ∧ Valid births selected ∧
      pendingAt (.selected history.length) selected = pendingAt source ledger ∧
      ∃ suffix, out.2 = (history ++ [takeRecord r]) ++ suffix ∧
        match out.1 with
        | .error _ => True
        | .ok ((_,w),a) => Post out.2 w a := by
  dsimp only
  intro queued submitted
  let selected := transferLocation (.staged generation r.pid peer.internalId) (.selected history.length) ledger
  have transfer := taken_held r run peer chosen valid before epoch history.length unused
  have held : Held selected generation r.pid peer history.length
      (history ++ [takeRecord r]) r.run.after r.run.ambientAfter :=
    transfer.2.2.1.views_append [takeRecord r] rfl rfl
  refine ⟨transfer.1,transfer.2.1,transfer.2.2.2,?_⟩
  have takeRun : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
      .ok ((some peer,r.run.after),r.run.ambientAfter) := by
    rw [←chosen]
    exact run
  have receipt : (⟨r.pid,⟨some peer,r.run.before,r.run.after,r.run.ambientBefore,r.run.ambientAfter⟩⟩ : Take.Receipt) = r := by
    cases r with
    | mk pid witness =>
      cases witness
      cases chosen
      rfl
  have selectionRun := runWGPrefix_receiptWGObserved (Take.observed takeRecord r.pid)
    (selectedRecord r.pid) r.run.before r.run.ambientBefore history
  rw [Take.observed_after_take takeRecord r.pid _ _ _ _ _ (some peer) takeRun,receipt,
    runWGPrefix_lift] at selectionRun
  change runWGPrefix (Take.selection takeRecord selectedRecord r.pid) _ _ _ = _ at selectionRun
  unfold staging
  simp only [runWGPrefix,runStatePrefix_bind]
  change runStatePrefix (Take.selection takeRecord selectedRecord r.pid) _ _ _ = _ at selectionRun
  rw [selectionRun]
  cases borrowRun : ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter with
  | error stop => exact ⟨[],by simp,True.intro⟩
  | ok out =>
    obtain ⟨⟨choice,v⟩,b⟩ := out
    have checked := borrow_held selected generation r.pid peer history.length
      r.run.after r.run.ambientAfter (history ++ [takeRecord r]) held
    obtain ⟨_,_,_,reached⟩ := checked
    have lifted := runWGPrefix_lift (Take.borrow (some peer))
      r.run.after r.run.ambientAfter (history ++ [takeRecord r])
    change runPrefix ((liftWGPrefix (Take.borrow (some peer))).run r.run.after)
      r.run.ambientAfter (history ++ [takeRecord r]) = _ at lifted
    rw [lifted,borrowRun] at reached
    obtain ⟨kid,rfl,afterBorrow⟩ := reached
    let event := selectedRecord r.pid ⟨some (peer,kid),r.run.before,v,r.run.ambientBefore,b⟩
    have afterEvent : Held selected generation r.pid peer history.length
        ((history ++ [takeRecord r]) ++ [event]) v b :=
      afterBorrow.views_append [event] rfl rfl
    have contract := checked_held selected generation r.pid peer history.length kid Post _ _
      (fun kp invalid => no_key_restores restoreRecord selected transfer.2.1 generation r.pid peer history.length
        kp invalid o native queue Post queued) submitted
    obtain ⟨suffix,extended,_,post⟩ := contract v b ((history ++ [takeRecord r]) ++ [event]) afterEvent
    refine ⟨[event] ++ suffix,?_,?_⟩
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
        | ok pair =>
          obtain ⟨⟨_,w⟩,a⟩ := pair
          exact id
      let actual := runWGPrefix
        (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
          (Restore.noKeyWith o (Restore.observed restoreRecord) queue r.pid peer.staged)
          (submit r.pid) r.pid peer kid) v b ((history ++ [takeRecord r]) ++ [event])
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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
