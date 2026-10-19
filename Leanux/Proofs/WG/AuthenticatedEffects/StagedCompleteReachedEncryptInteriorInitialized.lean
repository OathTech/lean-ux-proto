import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptLoopInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorLoop

/-! Native packet interiors reached from the initialized encryption caller.
The callback return retains its original world while the remaining packet
loop resumes at the actual read or byte-write point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open EncryptionPacket EncryptionInterior CompleteCarrier
variable {state : PacketState} {read : RunWitness DataPacket}

def returned (origin : World) (items : List SkbId) (body : PrefixM Event Bool) : PrefixM Event Bool :=
  fun w => ExceptT.mk fun history =>
    match runPrefix body w history with
    | (.error reason,last) => (.error reason,last)
    | (.ok (value,v),last) =>
        (.ok (value,v),last++[.old (.encryptionReturn (some items) ⟨value,origin,v⟩)])

theorem returned_congr (same : runPrefix left w history=runPrefix right v after) :
    runPrefix (returned origin items left) w history=runPrefix (returned origin items right) v after := by
  change (match runPrefix left w history with
    | (.error reason,last) => (Except.error reason,last)
    | (.ok (value,g),last) => (Except.ok (value,g),last++[Event.old (.encryptionReturn (some items) ⟨value,origin,g⟩)])) = _
  rw [same]
  rfl

def packetTail (origin : World) (items : List SkbId) (headId : SkbId)
    (head : RunWitness DataPacket) (rest : List SkbId)
    (body : PrefixM Event (ForInStep PacketState)) : PrefixM Event Bool :=
  returned origin items (body >>= fun choice =>
    (match choice with
      | .done state => pure state
      | .yield state => loop headId head rest state) >>= afterLoop items)

theorem Entry.loop_execution
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle)) :
    ∃ ledger, Accounted middle ledger [] [] u.wg ∧
      Execution headId head ledger [] [] items .crypted u middle
        (runPrefix (loop headId head items .crypted) u middle).1
        (runPrefix (loop headId head items .crypted) u middle).2 := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  have account := (head_prefix_current before captured).2.2.2.2.1
  exact ⟨ledger,account,execution account rfl⟩

theorem Entry.packet_account
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle))
    (walk : Walk headId head done .crypted u middle state v after) :
    ∃ ledger, Accounted after ledger [] [] v.wg := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,walk.accounted (head_prefix_current before captured).2.2.2.2.1⟩

theorem Entry.read_continuation
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle))
    (shape : items=done++skb::rest)
    (walk : Walk headId head done .crypted u middle state v after)
    (point : ReadPoint skb ledger [] [] v after read next last) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume next (packetTail world items headId head rest
        (crypt headId head skb read >>= afterCrypt skb state))) last := by
  rw [entry.packet_continuation captured shape walk]
  apply entry.resume_run_eq
  change runPrefix (returned world items (loop headId head (skb::rest) state >>= afterLoop items)) v after = _
  apply returned_congr
  rw [loop_cons,bind_assoc]
  exact Scheduler.bind_run_equal _ (point.continuation headId head state)

theorem Entry.write_continuation
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle))
    (shape : items=done++skb::rest)
    (walk : Walk headId head done .crypted u middle state v after)
    (point : WritePoint headId head skb ledger [] [] v after read encrypted next last) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume next (packetTail world items headId head rest
        (writeTail skb state encrypted))) last := by
  rw [entry.packet_continuation captured shape walk]
  apply entry.resume_run_eq
  change runPrefix (returned world items (loop headId head (skb::rest) state >>= afterLoop items)) v after = _
  apply returned_congr
  rw [loop_cons,bind_assoc]
  exact Scheduler.bind_run_equal _ (point.continuation state)

theorem Entry.read_point
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle))
    (walk : Walk headId head done .crypted u middle state v after)
    (performed : runPrefix (readPrefix skb) v after=(.ok (read,next),last)) :
    ∃ ledger, ReadPoint skb ledger [] [] v after read next last := by
  obtain ⟨ledger,before⟩ := entry.packet_account captured walk
  exact ⟨ledger,EncryptionInterior.read_point before performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
