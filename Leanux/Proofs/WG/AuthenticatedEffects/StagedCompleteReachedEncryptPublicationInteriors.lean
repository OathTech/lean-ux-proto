import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptInteriorInitialized

/-! Each fixed publication cut follows the actual initialized callback's
whole packet loop. The native setter and scheduling cuts precede the same
release child, with the original outer callback receipt still attached. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open EncryptionPacket EncryptionInterior
variable {state : PacketState}

theorem Entry.publication_interior_continuation
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (path : PublicationPath items world history ledger [] [] headId head state v after)
    (point : PublicationPoint site items state ledger [] [] v after first pid next last) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume next (returned world items (do
        publicationTailAt site first pid state
        pure true))) last := by
  rw [entry.publication_continuation path]
  apply entry.resume_run_eq
  change runPrefix (returned world items (publish items state)) v after = _
  apply returned_congr
  rw [publish,runPrefix_bind,point.continuation,runPrefix_bind]

theorem Entry.publication_interiors
    (entry : Entry trace placeholders operationIndex (some items) world history)
    (captured : runPrefix (headPrefix items) world history=(.ok ((headId,head),u),middle))
    (walked : runPrefix (loop headId head items .crypted) u middle=(.ok (state,g),after)) :
    ∃ ledger v, PublicationPath items world history ledger [] [] headId head state v after ∧
      ∀ site : PublicationSite,
        (∃ reason last, runPrefix (publicationPrefixAt site items state) v after=(.error reason,last) ∧
          runPrefix (ops.publish items state) v after=(.error reason,last)) ∨
        ∃ first pid next last, PublicationPoint site items state ledger [] [] v after first pid next last ∧
          CompleteConsequences.Cut last ledger [] [] next.wg ∧
          runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
            (fun result w=>(result,w)) trace placeholders) [] =
            runPrefixOuter (entry.resume next (returned world items (do
              publicationTailAt site first pid state
              pure true))) last := by
  obtain ⟨ledger,v,path⟩ := entry.publication_path captured walked
  refine ⟨ledger,v,path,?_⟩
  intro site
  rcases publication_points site items state path.accounted with failed | ⟨first,pid,next,last,point⟩
  · exact Or.inl failed
  · exact Or.inr ⟨first,pid,next,last,point,CompleteConsequences.accounted point.accounted,
      entry.publication_interior_continuation path point⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
