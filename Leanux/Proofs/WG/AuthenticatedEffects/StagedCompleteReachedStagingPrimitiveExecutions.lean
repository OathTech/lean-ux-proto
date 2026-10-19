import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveReservePoints

/-! Normal and stopped source decompositions retain the exact finite key
bind tree and the actual reserve read/write. An error has no invented world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
set_option maxHeartbeats 600000

inductive KeyExecution : {α : Type} → {action : WG.M α} → KeyShape action →
    WGWorld → Ambient → Except Stop ((α×WGWorld)×Ambient) → Prop where
  | pure (value : α) : KeyExecution (.pure value) w a (.ok ((value,w),a))
  | atom (token : KeyAtom α) (performed : (token.action.run w).run a=result) : KeyExecution (.atom token) w a result
  | stopped {body : WG.M α} {next : α → WG.M β} {head : KeyShape body} (tail : ∀ value,KeyShape (next value))
      (first : KeyExecution head w a (.error reason)) : KeyExecution (.bind head tail) w a (.error reason)
  | continued {body : WG.M α} {next : α → WG.M β} (head : KeyShape body) (tail : ∀ value,KeyShape (next value))
      (first : KeyExecution head w a (.ok ((value,u),b)))
      (later : KeyExecution (tail value) u b result) : KeyExecution (.bind head tail) w a result

theorem key_execution {action : WG.M α} (shape : KeyShape action) (w : WGWorld) (a : Ambient) : KeyExecution shape w a ((action.run w).run a) := by
  induction shape generalizing w a with
  | pure value=>exact .pure value
  | atom token=>exact .atom token rfl
  | bind head tail ihHead ihTail=>
    rename_i body next
    simp only [StateT.run_bind]
    cases leading : (body.run w).run a with
    | error reason=>exact .stopped tail (leading ▸ ihHead w a)
    | ok out=>obtain ⟨⟨value,u⟩,b⟩:=out; exact .continued head tail (leading ▸ ihHead w a) (ihTail value u b)

inductive ReserveExecution (kid : KeypairId) (w : WGWorld) (a : Ambient) (h : List Event) :
    Except Stop ((Nat×WGWorld)×Ambient) → List Event → Prop where
  | readStopped (run : ((getKeypair kid).run w).run a=.error reason) : ReserveExecution kid w a h (.error reason) h
  | writeStopped (read : ((getKeypair kid).run w).run a=.ok ((key,u),b))
      (write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b=.error reason) :
      ReserveExecution kid w a h (.error reason) h
  | normal (read : ((getKeypair kid).run w).run a=.ok ((key,u),b))
      (write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b=.ok (((),v),c)) :
      ReserveExecution kid w a h (.ok ((key.sendingCounter,v),c))
        ((h++[nonceEvent key])++[reservedEvent kid w v a c key])

theorem reserve_execution (kid : KeypairId) (w : WGWorld) (a : Ambient) (h : List Event) :
    let actual:=runWGPrefix (state (Journal.reserve kid)) w a h
    ReserveExecution kid w a h actual.1 actual.2 := by
  rw [reserve_factor]
  simp only [reserveObserved,reserveBody,runWGPrefix_receiptWGObserved,Staging.Points.run_bind,runWGPrefix_lift]
  cases read : ((getKeypair kid).run w).run a with
  | error reason=>exact .readStopped read
  | ok out=>
    obtain ⟨⟨key,u⟩,b⟩:=out
    dsimp only
    cases write : ((setKeypair kid {key with sendingCounter:=key.sendingCounter+1}).run u).run b with
    | error reason=>exact .writeStopped read write
    | ok out=>obtain ⟨⟨ignored,v⟩,c⟩:=out; cases ignored; exact .normal read write

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
