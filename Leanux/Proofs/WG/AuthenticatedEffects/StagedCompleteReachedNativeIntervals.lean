import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeCurrent

/-! The finite mutation intervals distinguish saved cohorts, allocation
aliases and native effects whose original receipt is still pending. These
constructors retain actual source evidence; none asserts an old resident
account after its packet or queue has been erased. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations RetirementSecurity AllocatedObligation CompleteCarrier

inductive Interval : History → WGWorld → Prop where
  | taking (cut : StagingPhase.PendingTake h ledger debts locals pid w a peer v b) : Interval h v
  | restoring (cut : StagingPhase.PendingRestore h ledger debts locals generation pid peer position w a v) : Interval h v
  | allocating (cut : Allocation.Interval h ledger debts locals generation pid peer position kid packets w a n items v) :
      Interval h v
  | keepalive (before : Accounted h ledger debts locals w)
      (device : w.dev=some d) (resident : d.peers[pid]?=some peer) (empty : peer.staged.isEmpty=true)
      (allocated : StagingInterior.keepaliveAllocation.run
        (StagingInterior.clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
      Interval h (StagingInterior.queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w)
  | purge {w : World} (before : Accounted h ledger debts locals w.wg)
      (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
      Interval h (Timer.Points.Purge.state pid p d w .cleared).wg
  | release (before : Accounted h ledger debts locals w)
      (native : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a=.ok ((value,v),b)) : Interval h v
  | nestedRelease {w : World} (before : Accounted h ledger debts locals w.wg)
      (native : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) : Interval middle v
  | nestedErase {w : World} (before : Accounted h ledger debts locals w.wg)
      (checked : runWGPrefix (NestedPeer.prefixAt NestedPeer.actual .checked peer) w.wg w.ambient h=
        (.ok ((some (pid,p),v),b),middle)) : Interval middle (NestedPeer.erasedWorld pid p.staged.length v)
  | createFree (cut : CreatePoints.FreeCut reason pid skb remaining h ledger debts locals w)
      (phase : CleanupPrimitive.Phase) : Interval (CleanupPrimitive.current phase w skb h) cut.after.wg
  | deadFree (waiting : CleanupPrimitive.Awaiting phase reason pid debts locals skb remaining w h ledger v after) :
      Interval (CleanupPrimitive.current phase w skb h) v.wg
  | socket (waiting : SocketInterior.Awaiting context skb rest packet peer ipv4 h ledger debts entry result frontWorld events) :
      Interval waiting.prior (SocketInterior.resultWorld frontWorld result).wg
  | trimLoop (cut : Transmit.Front.Residual.TrimCut h ledger debts locals pid w a n v b) : Interval h v
  | trimDrop (cut : Transmit.Front.Residual.TrimCut h ledger debts locals pid w a n v b)
      (device : v.dev=some d) (resident : d.peers[pid]?=some p)
      (excess : p.staged.length>MAX_STAGED_PACKETS) : Interval h (Transmit.Front.Residual.droppedWorld pid p d v)
  | trimReturned (before : Accounted h ledger debts locals w)
      (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) : Interval h v
  | routed (before : Accounted h ledger debts locals w)
      (path : Transmit.Path input h w a value v b middle) : Interval middle v

def Classified (h : History) (w : WGWorld) : Prop := Stable h w ∨ Interval h w

theorem Classified.of_accounted (before : Accounted h ledger debts locals w) : Classified h w :=
  Or.inl (Stable.of_accounted before)

theorem Classified.of_selected
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) : Classified h w :=
  Or.inl (Stable.of_selected before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
