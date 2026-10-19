import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePositive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDestructQuiescence
import Leanux.Proofs.WG.Lifetimes.DeviceLifecycle

/-! Exact source boundary for joining packet accounting and native reference
accounting at destruction. The observed preparation includes the real counted
removal callback; the checked tail includes the original device retirement. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
set_option maxHeartbeats 600000

/-- Literal observed preparation before the destructor's work guards. -/
def prepareObserved : WGPrefix Event Unit := do
  liftWGPrefix (modifyDev fun d=>{d with creatingNet:=false,incomingPort:=0})
  liftWGPrefix (socketReinit none none)
  Driver.removeAllObserved hooks

theorem prepare_erases : ErasesStatePrefix prepareObserved TxWork.Destruct.prepare := by
  unfold prepareObserved TxWork.Destruct.prepare
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>ConfigurationNative.remove_all_erases)

/-- The historical native finish alias is precisely check, settlement, reset
and retirement, with unchanged order and partial outcomes. -/
abbrev finish : WG.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish

theorem finish_factor : finish=CompleteRetired.tail := by
  unfold finish
  index_unfold _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish
  simp only [CompleteRetired.tail,TxWork.Destruct.check,TxWork.Destruct.settle,
    RetiredFrames.reset,bind_assoc]
  congr 1
  funext d
  split <;> split <;> simp only [bind_assoc,pure_bind]

/-- Exact actual causal destructor, including counted disposal receipts before
the native checked tail. This is a source equality, also on Stop. -/
theorem source_factor : Driver.destructObserved hooks=
    (prepareObserved >>= fun _=>liftWGPrefix CompleteRetired.tail) := by
  change Configuration.destructWith liftWGPrefix (Driver.removeAllObserved hooks)
    (liftWGPrefix finish)=_
  rw [finish_factor]
  simp only [Configuration.destructWith,prepareObserved,bind_assoc]

theorem erases : ErasesStatePrefix (Driver.destructObserved hooks) wgDestruct := by
  rw [source_factor,Lifecycle.destruct_factor]
  exact erasesStatePrefix_bind prepare_erases (fun _=>erasesStatePrefix_lift CompleteRetired.tail)

/-- Complete forward and converse packet accounting reaches the actual guard
entry; every release uses its actual counted successor ledger. -/
theorem prepare_checked : CompletePassive.Checked [] [] CompleteProduct.Safe prepareObserved := by
  have metadata : SameView StagedEntry.view
      (modifyDev fun d=>{d with creatingNet:=false,incomingPort:=0}) :=
    ReceiveFrames.device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  unfold prepareObserved
  apply StatePrefixEnsures.bind (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe _
    metadata)
  intro _
  apply StatePrefixEnsures.bind (CompletePassive.native CompleteProduct.Safe CompleteProduct.account_safe _
    (ControlFrames.socket (socketReinit_sameSocket none none)))
  intro _
  exact CompleteLifecycle.remove_all CompleteProduct.Safe CompleteProduct.account_safe

theorem allocated : Preserves StackOwnership.Allocated wgDestruct :=
  AllocatedFrames.observed (DeviceLifecycleCall.erases .destruct) (DeviceLifecycleCall.allocation .destruct)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle.Packet
