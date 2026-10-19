import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointKeepalive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmit

/-! Canonical local staging coverage has two distinct parts: fixed actual
source points/executions, and same-ledger semantic facts at named boundaries.
The endpoint history certificate does not reconstruct intermediate worlds.
Native atom interiors and the five named child families remain explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier
set_option maxHeartbeats 600000

/-- A point packages the actual native cut and its source-determined
continuation. The account belongs to the original invocation entry; the
cleared queue or pending birth is never given an unchanged idle account. -/
structure StagingPoint (history : History) (ledger : Ledger)
    (debts : List AllocatedObligation.CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (pid : PeerId) (w : WGWorld) (a : Ambient) : Type 1 where
  entry : Accounted history ledger debts locals w
  valueType : Type
  leaf : WGPrefix Event valueType
  world : WGWorld
  clock : Ambient
  journal : History
  remaining : WGPrefix Event Unit
  source : Point (stagingShape pid) w a history leaf world clock journal remaining

theorem StagingPoint.original
    (point : StagingPoint history ledger debts locals pid w a) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a history=
      runWGPrefix point.remaining point.world point.clock point.journal := point.source.residual

theorem staging_cases (pid : PeerId) (w : WGWorld) (a : Ambient) (h : History) :
    let actual:=runWGPrefix (Driver.stagingObserved hooks pid) w a h
    Execution (stagingShape pid) w a h actual.1 actual.2 :=
  execution_cases _ rfl

theorem keepalive_source_cases (pid : PeerId) (w : WGWorld) (a : Ambient) (h : History) :
    let actual:=runWGPrefix (Driver.keepaliveObserved hooks pid) w a h
    Execution (keepaliveShape pid) w a h actual.1 actual.2 :=
  execution_cases _ rfl

/-- Same actual normal/Stop execution and endpoint carrier, without callback
premises. Safe is explicitly the existing history certificate, not a claim
that each silent cut has an idle account or that its world is existential. -/
theorem staging_checked (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    let actual:=runWGPrefix (Driver.stagingObserved hooks pid) w a h
    Execution (stagingShape pid) w a h actual.1 actual.2 ∧
      CompleteTransmit.Safe debts actual.2 ∧
      match actual.1 with
      | .error _=>True
      | .ok (out,b)=>Carrier debts locals actual.2 out.2 b := by
  obtain ⟨_,_,safe,post⟩:=CompleteTransmit.staging (debts:=debts) (locals:=locals) pid w a h ⟨ledger,before⟩
  refine ⟨staging_cases pid w a h,safe,?_⟩
  dsimp only [runWGPrefix,runStatePrefix]
  cases result : runPrefix ((Driver.stagingObserved hooks pid).run w) a h with
  | mk out last=>
    cases out with
    | error=>trivial
    | ok pair=>
      obtain ⟨value,clock⟩:=pair
      simpa only [result] using post

/-- Preparation's same-successor account feeds the identical staging source;
reused queues and refused allocations keep their actual invocation events. -/
theorem keepalive_checked (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    let actual:=runWGPrefix (Driver.keepaliveObserved hooks pid) w a h
    Execution (keepaliveShape pid) w a h actual.1 actual.2 ∧
      CompleteTransmit.Safe debts actual.2 ∧
      match actual.1 with
      | .error _=>True
      | .ok (out,b)=>Carrier debts locals actual.2 out.2 b := by
  obtain ⟨_,_,safe,post⟩:=CompleteTransmit.keepalive (debts:=debts) (locals:=locals) pid w a h ⟨ledger,before⟩
  refine ⟨keepalive_source_cases pid w a h,safe,?_⟩
  dsimp only [runWGPrefix,runStatePrefix]
  cases result : runPrefix ((Driver.keepaliveObserved hooks pid).run w) a h with
  | mk out last=>
    cases out with
    | error=>trivial
    | ok pair=>
      obtain ⟨value,clock⟩:=pair
      simpa only [result] using post

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
