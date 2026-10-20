import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSendPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIPv6Composition

/-! The initialized runner obtains flushed protocol sending from the fixed
source and actual peer release. No sender callback contract is assumed here.
Remaining packet, dispatch and finer native-interval obligations stay visible. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def workPoints (other : WorkService.Points.ChildPoints) : WorkService.Points.ChildPoints :=
  fun token w h u middle=>match token with
    | .flushedSend pid=>RootPoint pid w h u middle
    | token=>other token w h u middle

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

noncomputable def senderContract
    (carrierGood : ∀h w,Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (pid : PeerId) : WorkService.Points.ChildSourceContract
      (Service.Expanded.workPoints (workPoints nativeWork))
      (Service.Expanded.workPoints (workPoints insideWork)) Good (.flushedSend pid) where
  remainder:=fun _ _ _ _ point=>ProtocolSend.remainder point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=fun _ _ _ _ before point=>root_safe carrierGood acceptPeer before point

/-- Initialized runner source cuts retain packet conservation through the
flushed handshake sender and its counted peer repayment, without an assumed
sender-source contract. The three remaining packet families, twelve dispatch
bodies and finer native interiors remain explicit coverage boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (IPv6.napiPoints nativeNapi))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (IPv6.napiPoints insideNapi))
      Good (.transmit family addr packets mtu))
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume
      (IPv6.napiPoints nativeNapi) (IPv6.napiPoints insideNapi) nativeWorker insideWorker Good)
    (dispatch : Service.Composition.DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints nativeNapi) nativeWorker (workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints insideNapi) insideWorker (workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints nativeNapi) nativeWorker (workPoints nativeWork))
        nativeDispatch) Good (Runner.Points.executeShape trace placeholders) [] :=
  IPv6.initialized trace placeholders carrierGood workGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive transmit workers (senderContract workGood acceptPeer) dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
