import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketFrontFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointResidual
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketSource

/-! Native socket cuts reuse the original route/cache/tunnel observer points.
Their erased continuation retains the actual source history and the original
entry used by the protocol socket receipt. No new native event is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

def unobserve (action : MixedM α) (h : List LifetimeEvent) : WG.M α :=
  fun w a=>(runWGPrefix action w a h).1

def front (args : ProtocolSocket.Args) : MixedM (Except Int SentDatagram) :=
  SocketInterior.beforeAppend args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4

theorem source_erases (args : ProtocolSocket.Args) :
    ErasesStatePrefix (front args >>= SocketInterior.appendResult) args.action := by
  unfold front
  rw [←SocketInterior.send_factor]
  unfold ProtocolSocket.Args.action
  cases ipv4 : args.ipv4 with
  | false=>exact send6Prefix_erases _ _ _ _ _
  | true=>exact send4Prefix_erases _ _ _ _ _

inductive Point (args : ProtocolSocket.Args) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | source (point : Prepare.Points.Point
      (SocketFront.canonical args.endpoint args.cache args.bytes args.ds args.exactRx args.ipv4)
      w a [] site v b middle remaining) : Point args w a v b
  | returned (performed : ((args.action.run w).run a)=.ok ((value,v),b)) : Point args w a v b

theorem Point.remaining (point : Point args w a v b) :
    ∃remaining : WG.M Int,((args.action.run w).run a)=(remaining.run v).run b := by
  cases point with
  | source point=>
      rename_i site middle remaining
      refine ⟨unobserve (remaining >>= SocketInterior.appendResult) middle,?_⟩
      rw [←source_erases args w a []]
      apply congrArg Prod.fst
      change runStatePrefix (front args >>= _) w a []=runStatePrefix (_ >>= _) v b _
      rw [runStatePrefix_bind,runStatePrefix_bind]
      have same := point.run
      change runStatePrefix _ w a []=runStatePrefix _ v b _ at same
      rw [show runStatePrefix (front args) w a []=runStatePrefix _ v b _ from same]
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point args w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E Int,runPrefix (liftWGObserver (liftWGPrefix args.action)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

theorem Point.receipt_remaining {E Context : Type} {w : World}
    (point : Point args w.wg w.ambient v b) (h : List E)
    (record : ProtocolSocket.Receipt Context → E) (context : Context) :
    ∃remaining : PrefixM E Int,runPrefix (liftWGObserver (ProtocolSocket.socket record context args)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (receiptWGObserved (liftWGPrefix rest) (fun run=>
    record ⟨context,args,{run with before:=w.wg,ambientBefore:=w.ambient}⟩)),?_⟩
  simp only [ProtocolSocket.socket,liftWGObserver_run,runWGPrefix_receiptWGObserved,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeSocket
