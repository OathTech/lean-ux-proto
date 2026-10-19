import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptPublicationInitialized

/-! Ordered encryption prefixes are reached after the same captured head.
Only actual yielded iterations permit another packet entry; the remaining
loop still publishes the original whole batch, including a later DEAD arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
variable {state : PacketState}

def packetPrefix (items : List SkbId) (count : Nat) :
    PrefixM Event (SkbId × RunWitness DataPacket × PacketState) := do
  let (headId,head) ← EncryptionPacket.headPrefix items
  let state ← EncryptionPacket.loop headId head (items.take count) .crypted
  pure (headId,head,state)

def loopTail (origin : World) (items : List SkbId) (headId : SkbId)
    (head : RunWitness DataPacket) (rest : List SkbId) (state : PacketState) : PrefixM Event Bool :=
  fun w => ExceptT.mk fun history =>
    match runPrefix (EncryptionPacket.loop headId head rest state >>= EncryptionPacket.afterLoop items) w history with
    | (.error reason,last) => (.error reason,last)
    | (.ok (value,v),last) =>
        (.ok (value,v),last++[.old (.encryptionReturn (some items) ⟨value,origin,v⟩)])

theorem Entry.packet_prefix_accounted
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (EncryptionPacket.headPrefix items) world history=(.ok ((headId,head),u),middle))
    (shape : items=done++rest)
    (walk : EncryptionPacket.Walk headId head done .crypted u middle state v after) :
    runPrefix (packetPrefix items done.length) world history=(.ok ((headId,head,state),v),after) ∧
      ∃ ledger, CompleteConsequences.Cut after ledger [] [] v.wg := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  obtain ⟨_,_,_,_,atHead,_⟩ := EncryptionPacket.head_prefix_current before captured
  refine ⟨?_,ledger,CompleteConsequences.accounted (walk.accounted atHead)⟩
  have taken : items.take done.length=done := by simpa using congrArg (List.take done.length) shape
  rw [packetPrefix,runPrefix_bind,captured]
  change runPrefix (EncryptionPacket.loop headId head (items.take done.length) .crypted >>=
    fun result=>pure (headId,head,result)) u middle = _
  rw [taken,runPrefix_bind,walk.run]
  rfl

theorem Entry.packet_continuation
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (EncryptionPacket.headPrefix items) world history=(.ok ((headId,head),u),middle))
    (shape : items=done++rest)
    (walk : EncryptionPacket.Walk headId head done .crypted u middle state v after) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume v (loopTail world items headId head rest state)) after := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  obtain ⟨selected,_,_,_,_,_⟩ := EncryptionPacket.head_prefix_current before captured
  have continued : runPrefix (EncryptionPacket.loop headId head items .crypted) u middle=
      runPrefix (EncryptionPacket.loop headId head rest state) v after := by
    rw [shape]
    exact walk.continuation rest
  rw [entry.original]
  apply entry.resume_run_eq
  change runPrefix (CausalJournal.encrypt (some items)) world history = _
  rw [EncryptionPacket.encrypt_run,EncryptionPacket.tail_factor items headId selected,runPrefix_bind,captured]
  dsimp only
  rw [EncryptionPacket.afterHead_factor,runPrefix_bind,continued]
  unfold loopTail
  change _ = (match runPrefix (EncryptionPacket.loop headId head rest state >>=
      EncryptionPacket.afterLoop items) v after with
    | (.error reason,last) => (Except.error reason,last)
    | (.ok (value,g),last) =>
      (Except.ok (value,g),last++[Event.old (.encryptionReturn (some items) ⟨value,world,g⟩)]))
  rw [runPrefix_bind]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
