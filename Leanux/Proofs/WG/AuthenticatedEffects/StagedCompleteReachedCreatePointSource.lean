import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationStops
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveRuns

/-! Literal create/admission source factors. Queue mutation precedes its
existing queued receipt, and the original ring/publication suffix remains
visible. No observer or native operation is added. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
open CausalJournal
set_option maxHeartbeats 600000

def body (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Unit :=
  Terminal.createObserved txEvent txEvent? CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items

def queueBefore (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event (Option Peer) := do
  let some first := items.head? | Admission.actualOps.step (invariant "an empty ring item")
  Admission.actualOps.access (setTxSkbPrefix first fun p=>{p with state:=.uncrypted})
  let peer ← Admission.actualOps.access (getPeerMixed pid)
  if ← Admission.actualOps.step (branch .enqueuePeerQueueFull (peer.txQueue.count ≥ MAX_QUEUED_PACKETS)) then
    return none
  return some peer

def queueWrite (pid : PeerId) (peer : Peer) (items : List SkbId) : PrefixM CausalJournal.Event Unit :=
  Admission.actualOps.access (setPeerMixed pid {peer with txQueue:=peer.txQueue.enqueue items})

def queueInstall (pid : PeerId) (peer : Peer) (items : List SkbId) : PrefixM CausalJournal.Event Unit := do
  queueWrite pid peer items
  Admission.actualOps.event (.queued pid items)

def queueAfter (items : List SkbId) : PrefixM CausalJournal.Event Int := do
  let d ← Admission.actualOps.step getDev
  let cpu ← Admission.actualOps.step (cpumaskNextOnlineFrom d.encryptLastCpu)
  Admission.actualOps.step (modifyDev fun d=>{d with encryptLastCpu:=cpu})
  if ← Admission.actualOps.step (branch .enqueueRingFull d.encryptQueue.full) then return -WG.EPIPE
  Admission.actualOps.step (queueDeviceWork .encryptWorker)
  Admission.actualOps.step (modifyDev fun d=>{d with encryptQueue:=d.encryptQueue.produce items})
  return 0

def offered (items : List SkbId) (ret : Int) : PrefixM CausalJournal.Event Int := do
  if ret=0 then Admission.actualOps.event (.ring (.offered items true))
  else if ret = -WG.EPIPE then Admission.actualOps.event (.ring (.offered items false))
  return ret

private theorem step_focus (action : WG.M α) :
    CausalFocus.Aligned txEvent txEvent? (Admission.actualOps.step action) (liftPrefix (liftWG action)) :=
  ⟨Appends.lift _,rfl⟩

private theorem access_focus (action : MixedM α) :
    CausalFocus.Aligned txEvent txEvent? (Admission.actualOps.access action) (TxDisposition.nativeAccess action) :=
  ⟨Appends.focus _ _ _,rfl⟩

private theorem event_focus (event : TxDisposition.Event) :
    CausalFocus.Aligned txEvent txEvent? (Admission.actualOps.event event) (emitPrefix event) :=
  ⟨fun _ _=>⟨[event],rfl⟩,rfl⟩

theorem before_factor (pid : PeerId) (items : List SkbId) :
    QueueHandoff.focused (QueueHandoff.before pid items)=queueBefore pid items := by
  symm
  apply And.right (a:=Appends (QueueHandoff.before pid items))
  change CausalFocus.Aligned txEvent txEvent? (queueBefore pid items) (QueueHandoff.before pid items)
  unfold queueBefore QueueHandoff.before
  cases items.head? <;>
    repeat' first
      | exact step_focus _
      | exact access_focus _
      | exact CausalFocus.pure txEvent txEvent? _
      | apply CausalFocus.bind txEvent txEvent? (fun _=>rfl)
      | intro _
      | dsimp (config:={failIfUnchanged:=true}) only
      | split

theorem install_factor (pid : PeerId) (peer : Peer) (items : List SkbId) :
    QueueHandoff.focused (QueueHandoff.install pid peer items)=queueInstall pid peer items :=
  (CausalFocus.bind txEvent txEvent? (fun _=>rfl)
    (access_focus (setPeerMixed pid {peer with txQueue:=peer.txQueue.enqueue items}))
    (fun _=>event_focus (.queued pid items))).2.symm

theorem after_factor (items : List SkbId) :
    QueueHandoff.focused (QueueHandoff.after items)=queueAfter items := by
  symm
  apply And.right (a:=Appends (QueueHandoff.after items))
  change CausalFocus.Aligned txEvent txEvent? (queueAfter items) (QueueHandoff.after items)
  unfold queueAfter QueueHandoff.after
  repeat' first
    | exact step_focus _
    | exact CausalFocus.pure txEvent txEvent? _
    | apply CausalFocus.bind txEvent txEvent? (fun _=>rfl)
    | intro _
    | dsimp (config:={failIfUnchanged:=true}) only
    | split

theorem offered_factor (items : List SkbId) (ret : Int) :
    QueueHandoff.focused (QueueHandoff.offered items ret)=offered items ret := by
  symm
  apply And.right (a:=Appends (QueueHandoff.offered items ret))
  change CausalFocus.Aligned txEvent txEvent? (offered items ret) (QueueHandoff.offered items ret)
  unfold offered QueueHandoff.offered
  split <;> try split
  all_goals repeat' first
    | exact event_focus _
    | exact CausalFocus.pure txEvent txEvent? _
    | apply CausalFocus.bind txEvent txEvent? (fun _=>rfl)
    | intro _

def enqueue (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Int :=
  (do let some peer ← queueBefore pid items | pure (-WG.ENOSPC)
      queueInstall pid peer items
      queueAfter items) >>= offered items

theorem enqueue_factor (pid : PeerId) (items : List SkbId) :
    Admission.actualOps.enqueue pid items=enqueue pid items := by
  rw [QueueHandoff.actual_enqueue]
  simp only [QueueHandoff.enqueueFocused,before_factor,install_factor,after_factor,offered_factor,enqueue]
  rfl

theorem lower_factor (pid : PeerId) (items : List SkbId) :
    CausalJournal.create pid items=NativeAdapter.lower (body pid items) := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
