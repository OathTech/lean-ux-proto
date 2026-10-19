import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct

/-! The fixed enriched transmit source, ending at the actual staging caller.
Input, disposal and routed receipts belong to the same front execution. The
original post-staging reference repayment remains in its continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

abbrev Input := StagedAdmission.Front.Input

def body (input : Input) : WGPrefix Event (Except Int PeerId) :=
  StagedAdmission.Front.body input.family input.address input.packets input.mtu

def inputHistory (input : Input) (h : List Event) : List Event := h++[.transmitInput input]

def receipt (value : Except Int PeerId) (w v : WGWorld) (a b : Ambient) : WGRunWitness (Except Int PeerId) :=
  ⟨value,w,v,a,b⟩

def resultHistory (input : Input) (value : Except Int PeerId) (w v : WGWorld) (a b : Ambient)
    (prior : List Event) : List Event :=
  prior++[StagedAdmission.Front.routedEvent input (receipt value w v a b)]

def repayment (pid : PeerId) : WGPrefix Event Int := do
  hooks.peerRelease (some pid)
  pure 0

def tail : Except Int PeerId → WGPrefix Event Int
  | .error err=>pure err
  | .ok pid=>Driver.stagingObserved hooks pid >>= fun _=>repayment pid

theorem factor (input : Input) :
    Driver.transmitObserved hooks input.family input.address input.packets input.mtu=
      (CausalJournal.front input.family input.address input.packets input.mtu >>= tail) := rfl

theorem front_run (input : Input) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h=
      match runWGPrefix (body input) w a (inputHistory input h) with
      | (.error stop,last)=>(.error stop,last)
      | (.ok ((value,v),b),prior)=>(.ok ((value,v),b),resultHistory input value w v a b prior) :=
  StagedAdmission.Front.front_run input w a h

/-- The next fixed source prefix includes the original take/key/nonce path,
but stops before its actual allocation/no-key continuation. -/
def stagingPrefix (input : Input) : WGPrefix Event (Except Int (PeerId×Option (Peer×Staging.Decision))) := do
  match ← CausalJournal.front input.family input.address input.packets input.mtu with
  | .error err=>pure (.error err)
  | .ok pid=>do
    let chosen←Staging.stagingPrefix pid
    pure (.ok (pid,chosen))

def stagingTail : Except Int (PeerId×Option (Peer×Staging.Decision))→WGPrefix Event Int
  | .error err=>pure err
  | .ok (pid,chosen)=>Staging.stagingTail pid chosen >>= fun _=>repayment pid

theorem staging_factor (input : Input) :
    Driver.transmitObserved hooks input.family input.address input.packets input.mtu=
      (stagingPrefix input >>= stagingTail) := by
  rw [factor]
  simp only [stagingPrefix,bind_assoc]
  congr 1
  funext value
  cases value with
  | error err=>simp only [tail,pure_bind,stagingTail]
  | ok pid=>simp only [tail,Staging.whole_factor,bind_assoc,pure_bind,stagingTail]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
