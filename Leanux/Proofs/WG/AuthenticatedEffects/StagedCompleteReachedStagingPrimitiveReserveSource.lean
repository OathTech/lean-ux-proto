import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveKeyCoverage

/-! The two existing reservation receipts are separated from the native
counter write. The saved before-world belongs to this reservation invocation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations
set_option maxHeartbeats 600000

def reserveBody (kid : KeypairId) : WGPrefix Event Nat := do
  let key←liftWGPrefix (getKeypair kid)
  liftWGPrefix (setKeypair kid {key with sendingCounter:=key.sendingCounter+1})
  emitStatePrefix (.old (.nonce (Nonce.allocation (Nonce.cell key))))
  pure key.sendingCounter

def reserveObserved (kid : KeypairId) : WGPrefix Event Nat :=
  receiptWGObserved (reserveBody kid) (fun run=>.old (.reserved kid run))

theorem focus_run (encode : E → F) (decode : F → Option E) (body : WGPrefix E α)
    (w : WGWorld) (a : Ambient) (h : List F) :
    runWGPrefix (focusStatePrefix encode decode body) w a h=
      ((runWGPrefix body w a (h.filterMap decode)).1,
        h++((runWGPrefix body w a (h.filterMap decode)).2.drop (h.filterMap decode).length).map encode) := rfl

theorem reserve_factor (kid : KeypairId) : state (Journal.reserve kid)=reserveObserved kid := by
  funext w a h
  change runWGPrefix (state (Journal.reserve kid)) w a h=runWGPrefix (reserveObserved kid) w a h
  simp only [state,Journal.reserve,reserveObserved,focus_run,runWGPrefix_receiptWGObserved]
  simp only [runWGPrefix,Nonce.reserveObserved,reserveBody,runStatePrefix_bind,
    liftWGPrefix,runStatePrefix_lift,runStatePrefix_emit,runStatePrefix_pure]
  cases read : ((getKeypair kid).run w).run a with
  | error reason=>simp only [List.drop_length,List.map_nil,List.append_nil]
  | ok out=>
    obtain ⟨⟨key,u⟩,b⟩:=out
    dsimp only
    cases written : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b with
    | error reason=>simp only [List.drop_length,List.map_nil,List.append_nil]
    | ok out=>
      obtain ⟨⟨ignored,v⟩,c⟩:=out
      cases ignored
      simp only [List.drop_left,List.map_append,List.map_cons,List.map_nil,List.append_assoc]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
