import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeReceiptStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeReceiptDisposal

/-! Only the original named pending records may close a receipt interval.
The completed history is indexed by the actual native source witness and
its captured entry, not by an arbitrary future history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations RetirementSecurity AllocatedObligation CompleteCarrier

inductive RecordsDue : History → WGWorld → History → Prop where
  | taking (cut : StagingPhase.PendingTake h ledger debts locals pid w a peer v b) :
      RecordsDue h v (h++[.stagingTaken ⟨pid,⟨some peer,w,v,a,b⟩⟩])
  | restoring (cut : StagingPhase.PendingRestore h ledger debts locals generation pid peer position w a v) :
      RecordsDue h v (h++[.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩])
  | keepalive (before : Accounted h ledger debts locals w)
      (device : w.dev=some d) (resident : d.peers[pid]?=some peer) (empty : peer.staged.isEmpty=true)
      (allocated : StagingInterior.keepaliveAllocation.run
        (StagingInterior.clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
      RecordsDue h (StagingInterior.queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w)
        (h++[StagingInterior.keepaliveEvent pid true w
          (StagingInterior.queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w) a b])
  | purge {w : World} (before : Accounted h ledger debts locals w.wg)
      (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
      RecordsDue h (Timer.Points.Purge.state pid p d w .cleared).wg
        (Timer.Points.Purge.history pid p d w h .recorded)
  | release (before : Accounted h ledger debts locals w)
      (native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a=.ok ((value,v),b)) :
      RecordsDue h v (h++[PeerRetirement.releaseEvent peer value w v a b])
  | nestedRelease {w : World} (before : Accounted h ledger debts locals w.wg)
      (native : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
      RecordsDue middle v (middle++[PeerRelease.receipt peer value w.wg v w.ambient b])
  | nestedErase {w : World} (before : Accounted h ledger debts locals w.wg)
      (checked : runWGPrefix (NestedPeer.prefixAt NestedPeer.actual .checked peer) w.wg w.ambient h=
        (.ok ((some (pid,p),v),b),middle)) :
      RecordsDue middle (NestedPeer.erasedWorld pid p.staged.length v)
        (middle++NestedPeer.eraseEvents v pid++[PeerRelease.receipt peer (some (pid,p))
          w.wg (NestedPeer.erasedWorld pid p.staged.length v) w.ambient b])
  | createFree (cut : CreatePoints.FreeCut reason pid skb remaining h ledger debts locals w)
      (phase : CleanupPrimitive.Phase) :
      RecordsDue (CleanupPrimitive.current phase w skb h) cut.after.wg
        (CleanupPrimitive.finished reason skb w cut.after h)
  | deadFree (waiting : CleanupPrimitive.Awaiting phase reason pid debts locals skb remaining w h ledger v after) :
      RecordsDue (CleanupPrimitive.current phase w skb h) v.wg (CleanupPrimitive.finished reason skb w v h)
  | socket (waiting : SocketInterior.Awaiting context skb rest packet peer ipv4 h ledger debts entry result frontWorld events) :
      RecordsDue waiting.prior (SocketInterior.resultWorld frontWorld result).wg
        (waiting.prior++[.old (.socket (SocketInterior.receipt context.pid skb packet peer ipv4 entry result frontWorld))])
  | trimReturned (before : Accounted h ledger debts locals w)
      (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) :
      RecordsDue h v (h++[.stagedDisposal (.overflow pid ⟨(),w,v,a,b⟩)])
  | routed (before : Accounted h ledger debts locals w)
      (path : Transmit.Path input h w a value v b middle) :
      RecordsDue middle v (Transmit.resultHistory input value w v a b middle)

private theorem cleanup_prefix (phase : CleanupPrimitive.Phase)
    (reason : HandshakeSecurity.StagedConservation.Terminal.Reason)
    (skb : SkbId) (w v : World) (h : History) :
    ∃suffix,CleanupPrimitive.finished reason skb w v h=CleanupPrimitive.current phase w skb h++suffix := by
  cases phase with
  | mutated=>
      refine ⟨[CleanupPrimitive.releaseEvent w.wg skb,.terminalDrop (CleanupPrimitive.receipt reason skb w v)],?_⟩
      simp only [CleanupPrimitive.finished,CleanupPrimitive.current,List.append_assoc,List.cons_append,List.nil_append]
  | released=>
      refine ⟨[.terminalDrop (CleanupPrimitive.receipt reason skb w v)],?_⟩
      simp only [CleanupPrimitive.finished,CleanupPrimitive.current,List.append_assoc,List.cons_append,List.nil_append]

theorem RecordsDue.prefix (due : RecordsDue h w last) : ∃suffix,last=h++suffix := by
  cases due with
  | nestedErase before checked=>exact ⟨_,List.append_assoc ..⟩
  | createFree cut phase=>exact cleanup_prefix phase _ _ _ _ _
  | deadFree waiting=>exact cleanup_prefix _ _ _ _ _ _
  | taking | restoring | keepalive | purge | release | nestedRelease | socket | trimReturned | routed=>exact ⟨_,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
