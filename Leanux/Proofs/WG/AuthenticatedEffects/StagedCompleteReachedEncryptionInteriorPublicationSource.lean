import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorPacketCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPublicationFrames

/-! The encryption callback's actual withRelease publication. This source
does not emit the disposition observer's published event. The original queue
check and head setter are separate, before CPU selection and repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open EncryptionPacket

def queueCheck (pid : PeerId) (first : SkbId) : WG.M Unit := do
  if !((← getPeer pid).txQueue.all.any (·.head? == some first)) then
    invariant "an item for the tx worker that is not on its peer's tx_queue"

def scheduleNative (pid : PeerId) : WG.M Unit := do
  _ ← cpumaskChooseOnline pid
  if !(← getDev).txWorkQueue.contains pid || (← peekQueuedUnit .txWorker pid) then
    recordQueued .txWorker pid
    modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}

theorem middle_factor (pid : PeerId) (first : SkbId) (state : PacketState) :
    TxDisposition.publicationMiddle pid first state = (do
      queueCheck pid first
      setTxSkb first fun p => {p with state}
      scheduleNative pid) := by
  simp only [TxDisposition.publicationMiddle,queueCheck,scheduleNative,bind_assoc,TxDisposition.bind_ite,pure_bind]

def borrow (items : List SkbId) : PrefixM CausalJournal.Event (SkbId × PeerId) :=
  liftPrefix (liftWG (AllocatedObligation.Publication.borrowNative items))

def check (pid : PeerId) (first : SkbId) : PrefixM CausalJournal.Event Unit :=
  liftPrefix (liftWG (queueCheck pid first))

def mark (first : SkbId) (state : PacketState) : PrefixM CausalJournal.Event Unit :=
  liftPrefix (liftWG (setTxSkb first fun p => {p with state}))

def schedule (pid : PeerId) : PrefixM CausalJournal.Event Unit := liftPrefix (liftWG (scheduleNative pid))

def release (pid : PeerId) : PrefixM CausalJournal.Event Unit :=
  liftWGObserver (CausalJournal.peerRelease (some pid))

theorem publish_factor (items : List SkbId) (state : PacketState) :
    ops.publish items state = (do
      let (first,pid) ← borrow items
      check pid first
      mark first state
      schedule pid
      release pid) := by
  change liftWGObserver (HandshakeSecurity.StagedDisposal.Publication.observed
    CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal? items state) = _
  rw [CompleteEncrypt.publication_factor]
  simp only [middle_factor,Queued.lift_bind,liftWGObserver_bind,liftWGObserver_lift,bind_assoc]
  rfl

inductive PublicationSite where
  | borrowed | checked | marked | scheduled

def publicationPrefixAt (site : PublicationSite) (items : List SkbId) (state : PacketState) :
    PrefixM CausalJournal.Event (SkbId × PeerId) := do
  let (first,pid) ← borrow items
  match site with
  | .borrowed => pure (first,pid)
  | .checked => check pid first; pure (first,pid)
  | .marked => check pid first; mark first state; pure (first,pid)
  | .scheduled => check pid first; mark first state; schedule pid; pure (first,pid)

def publicationTailAt (site : PublicationSite) (first : SkbId) (pid : PeerId) (state : PacketState) :
    PrefixM CausalJournal.Event Unit := do
  match site with
  | .borrowed => check pid first; mark first state; schedule pid; release pid
  | .checked => mark first state; schedule pid; release pid
  | .marked => schedule pid; release pid
  | .scheduled => release pid

/-- Each point is a literal original prefix, including the point immediately
after the head mutation and before any scheduling or release receipt. -/
theorem publication_point_factor (site : PublicationSite) (items : List SkbId) (state : PacketState) :
    ops.publish items state =
      (publicationPrefixAt site items state >>= fun (first,pid) => publicationTailAt site first pid state) := by
  rw [publish_factor]
  cases site <;> simp only [publicationPrefixAt,publicationTailAt,bind_assoc,pure_bind]

theorem publication_continuation (performed : runPrefix (publicationPrefixAt site items state) w history =
    (.ok ((first,pid),v),after)) :
    runPrefix (ops.publish items state) w history = runPrefix (publicationTailAt site first pid state) v after := by
  rw [publication_point_factor site,runPrefix_bind,performed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
