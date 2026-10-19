import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldSource

/-! One actual selection-source proof, parameterized only by the carried
property and its local native contracts. It does not abstract the choice
of peer, receipt order or nonce-checking code. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SelectionCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal
open HandshakeSecurity.StagedConservation

theorem after_take (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (P : List Event → WGWorld → Ambient → Prop) (Safe : List Event → Prop)
    (safeP : ∀ h w a, P h w a → Safe h)
    (held : P (history ++ [.stagingTaken r]) r.run.after r.run.ambientAfter)
    (borrowed : StatePrefixEnsures P Safe (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a => ∃ keypair, selected = some (peer,keypair) ∧ P h w a))
    (selected : ∀ h w a (run : WGRunWitness (Option (Peer × Option KeypairId))),
      P h w a → P (h ++ [Event.old (.responder (.selected r.pid run))]) w a)
    (Post : List Event → WGWorld → Ambient → Prop)
    (checked : ∀ keypair, StatePrefixEnsures P Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
        (HeldSource.noKey r.pid peer) (HeldSource.submit r.pid) r.pid peer keypair) (fun _ => Post)) :
    let out := runWGPrefix (Driver.stagingObserved hooks r.pid) r.run.before r.run.ambientBefore history
    ∃ suffix, out.2 = (history ++ [.stagingTaken r]) ++ suffix ∧ Safe out.2 ∧
      match out.1 with
      | .error _ => True
      | .ok ((_,w),a) => Post out.2 w a := by
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
  rw [HeldSource.staging_factor]
  simp only [runWGPrefix,runStatePrefix_bind]
  change runStatePrefix (CausalJournal.selection r.pid) _ _ _ = _ at selectionRun
  rw [selectionRun]
  cases borrowRun : ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter with
  | error stop => exact ⟨[],by simp,safeP _ _ _ held,True.intro⟩
  | ok out =>
    obtain ⟨⟨choice,v⟩,b⟩ := out
    obtain ⟨_,_,_,reached⟩ := borrowed
      r.run.after r.run.ambientAfter (history ++ [.stagingTaken r]) held
    have lifted := runWGPrefix_lift (Take.borrow (some peer))
      r.run.after r.run.ambientAfter (history ++ [.stagingTaken r])
    change runPrefix ((liftWGPrefix (Take.borrow (some peer))).run r.run.after)
      r.run.ambientAfter (history ++ [.stagingTaken r]) = _ at lifted
    rw [lifted,borrowRun] at reached
    obtain ⟨kid,rfl,afterBorrow⟩ := reached
    let event := Event.old (.responder (.selected r.pid
      ⟨some (peer,kid),r.run.before,v,r.run.ambientBefore,b⟩))
    have afterEvent : P ((history ++ [.stagingTaken r]) ++ [event]) v b :=
      selected _ _ _ _ afterBorrow
    have checked := checked kid
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
          (HeldSource.noKey r.pid peer) (HeldSource.submit r.pid) r.pid peer kid)
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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SelectionCarrier
