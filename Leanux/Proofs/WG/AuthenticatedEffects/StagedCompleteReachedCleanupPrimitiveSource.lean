import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadIntervalWorker

/-! The fixed original getter, erase and receipt-emission sequence. The
native erase precedes the lifetime release marker and labelled receipt;
both remaining emissions are total and leave the native world unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedConservation

def readEvent (w : WGWorld) (skb : SkbId) : CausalJournal.Event :=
  CausalJournal.txEvent (.access (.packet (.read (.inl skb) (packetStamp w skb))))

def releaseEvent (w : WGWorld) (skb : SkbId) : CausalJournal.Event :=
  CausalJournal.txEvent (.access (.packet (.release (.inl skb) (packetStamp w skb))))

def readPrefix (entry : World) (skb : SkbId) : PrefixM CausalJournal.Event Unit := do
  _ ← liftPrefix (liftWG (getTxSkb skb))
  emitPrefix (readEvent entry.wg skb)

def mutationPrefix (entry : World) (skb : SkbId) : PrefixM CausalJournal.Event Unit := do
  readPrefix entry skb
  liftPrefix (liftWG (modifyDev (erasePacketDevice (.inl skb))))

def releasedPrefix (entry : World) (skb : SkbId) : PrefixM CausalJournal.Event Unit := do
  mutationPrefix entry skb
  emitPrefix (releaseEvent entry.wg skb)

inductive Phase where
  | mutated
  | released

def current (phase : Phase) (w : World) (skb : SkbId) (history : List CausalJournal.Event) :=
  match phase with
  | .mutated => history ++ [readEvent w.wg skb]
  | .released => history ++ [readEvent w.wg skb,releaseEvent w.wg skb]

def atPhase (phase : Phase) (w : World) (skb : SkbId) : PrefixM CausalJournal.Event Unit :=
  match phase with
  | .mutated => mutationPrefix w skb
  | .released => releasedPrefix w skb

def receipt (reason : Terminal.Reason) (skb : SkbId) (w v : World) : Terminal.Receipt :=
  ⟨reason,skb,⟨(),w,v⟩⟩

def finished (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history : List CausalJournal.Event) : List CausalJournal.Event :=
  history ++ [readEvent w.wg skb,releaseEvent w.wg skb,.terminalDrop (receipt reason skb w v)]

def due (phase : Phase) (reason : Terminal.Reason) (skb : SkbId) (w v : World) :
    PrefixM CausalJournal.Event Unit := do
  match phase with
  | .mutated => emitPrefix (releaseEvent w.wg skb)
  | .released => pure ()
  emitPrefix (.terminalDrop (receipt reason skb w v))

theorem due_run (phase : Phase) (reason : Terminal.Reason) (skb : SkbId) (w v : World)
    (history : List CausalJournal.Event) :
    runPrefix (due phase reason skb w v) v (current phase w skb history) =
      (.ok ((),v),finished reason skb w v history) := by
  cases phase <;> simp [due,current,finished,runPrefix_bind,runPrefix_emit,List.append_assoc]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
