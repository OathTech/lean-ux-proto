import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeRecordsSource

/-! Each named pending-record sequence completes the semantic current-state
account on the same WG projection, without another native operation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem RecordsDue.accounted (due : RecordsDue h w last) : Stable last w := by
  cases due with
  | taking cut=>
      obtain ⟨after,current⟩:=(Receipt.taking cut).1
      exact ⟨after,_,_,current⟩
  | restoring cut=>
      obtain ⟨after,current⟩:=(Receipt.restoring cut).1
      exact ⟨after,_,_,current⟩
  | keepalive before device resident empty allocated=>
      obtain ⟨after,current⟩:=(Receipt.keepalive before device resident empty allocated).1
      exact ⟨after,_,_,current⟩
  | purge before device resident=>
      obtain ⟨after,current⟩:=(Receipt.purge before device resident).1
      exact ⟨after,_,_,current⟩
  | release before native=>
      obtain ⟨after,current⟩:=(Receipt.release before native).1
      exact ⟨after,_,_,current⟩
  | nestedRelease before native=>
      obtain ⟨after,current⟩:=(Receipt.nested_release before native).1
      exact ⟨after,_,_,current⟩
  | nestedErase before checked=>
      obtain ⟨after,current⟩:=(Receipt.nested_erase before checked).1
      exact ⟨after,_,_,current⟩
  | createFree cut phase=>exact ⟨_,_,_,(Receipt.create_free cut phase).1⟩
  | deadFree waiting=>exact ⟨_,_,_,(Receipt.dead_free waiting).1⟩
  | socket waiting=>exact (Receipt.socket waiting).1
  | trimReturned before performed=>
      obtain ⟨after,current⟩:=(Receipt.trimmed before performed).1
      exact ⟨after,_,_,current⟩
  | routed before path=>
      obtain ⟨after,current⟩:=(Receipt.routed before path).1
      exact ⟨after,_,_,current⟩

def emitRecords : List Event → WGPrefix Event Unit
  | []=>pure ()
  | event::rest=>emitStatePrefix event >>= fun _=>emitRecords rest

theorem emitRecords_run (records : List Event) (w : WGWorld) (a : Ambient) (h : History) :
    runWGPrefix (emitRecords records) w a h=(.ok (((),w),a),h++records) := by
  induction records generalizing h with
  | nil=>simp only [List.append_nil]; rfl
  | cons event rest ih=>
      change runStatePrefix (_ >>= _) w a h=_
      rw [runStatePrefix_bind,runStatePrefix_emit]
      simpa only [runWGPrefix,runStatePrefix,List.append_assoc,List.cons_append,List.nil_append]
        using ih (h++[event])

/-- Security: the original pending records complete without changing the
native world, and their precise extended history carries a full ticket
partition, native cell ownership and receipt counts on one ledger. -/
theorem RecordsDue.close (due : RecordsDue h w last) (a : Ambient) :
    ∃records,last=h++records ∧
      runWGPrefix (emitRecords records) w a h=(.ok (((),w),a),last) ∧ Stable last w := by
  obtain ⟨records,extended⟩:=due.prefix
  exact ⟨records,extended,by rw [emitRecords_run,←extended],due.accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
