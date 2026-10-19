import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPacketEntry

/-! The original initialized encryption callback reaches publication after
its captured head and actual packet loop. Its enclosing receipt retains the
callback's original before-world, even though execution resumes later. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
variable {state : PacketState}

def publicationTail (origin : World) (items : List SkbId) (state : PacketState) : PrefixM Event Bool :=
  fun w => ExceptT.mk fun history =>
    match runPrefix (EncryptionPacket.publish items state) w history with
    | (.error reason,last) => (.error reason,last)
    | (.ok (value,v),last) =>
        (.ok (value,v),last++[.old (.encryptionReturn (some items) ⟨value,origin,v⟩)])

theorem Entry.publication_path
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (EncryptionPacket.headPrefix items) world history=(.ok ((headId,head),u),middle))
    (walked : runPrefix (EncryptionPacket.loop headId head items .crypted) u middle=(.ok (state,g),after)) :
    ∃ ledger v, EncryptionPacket.PublicationPath items world history ledger [] [] headId head state v after := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  obtain ⟨v,path⟩ := EncryptionPacket.publication_path before captured walked
  exact ⟨ledger,v,path⟩

theorem Entry.publication_accounted
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (EncryptionPacket.headPrefix items) world history=(.ok ((headId,head),u),middle))
    (walked : runPrefix (EncryptionPacket.loop headId head items .crypted) u middle=(.ok (state,g),after)) :
    ∃ ledger v,
      runPrefix (EncryptionPacket.callbackPublicationPrefix items) world history=
        (.ok ((headId,head,state),v),after) ∧
      CompleteConsequences.Cut after ledger [] [] v.wg := by
  obtain ⟨ledger,v,path⟩ := entry.publication_path captured walked
  exact ⟨ledger,v,path.performed,CompleteConsequences.accounted path.accounted⟩

theorem Entry.publication_continuation
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (path : EncryptionPacket.PublicationPath items world history ledger [] [] headId head state v after) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume v (publicationTail world items state)) after := by
  rw [entry.original]
  apply entry.resume_run_eq
  change runPrefix (CausalJournal.encrypt (some items)) world history = _
  exact path.original

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
