import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionReturned

/-! Native queue selection points follow the original peer reads, queue
choice and setter. The queue's cached representation keeps ownership until
the dequeue setter transfers the selected batch into the worker local. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation

def peekChoice (pid : PeerId) : WG.M (Option (List SkbId) × PrevQueue (List SkbId)) := do
  (← getPeer pid).txQueue.peek

def peekRead (pid : PeerId) : WG.M ((Option (List SkbId) × PrevQueue (List SkbId)) × Peer) := do
  let selected ← peekChoice pid
  let peer ← getPeer pid
  pure (selected,peer)

def peekWrite (pid : PeerId) (read : (Option (List SkbId) × PrevQueue (List SkbId)) × Peer) : WG.M Unit :=
  setPeer pid {read.2 with txQueue := read.1.2}

def peekTail (pid : PeerId) (read : (Option (List SkbId) × PrevQueue (List SkbId)) × Peer) :
    WG.M (Option (List SkbId)) := do
  peekWrite pid read
  pure read.1.1

theorem peek_factor (pid : PeerId) : txPeekSource pid=peekRead pid >>= peekTail pid := by
  simp only [txPeekSource,peekRead,peekChoice,peekTail,peekWrite,bind_assoc,pure_bind]

def dropRead (pid : PeerId) : WG.M (Peer × Peer) := do
  let stored ← getPeer pid
  let queued ← getPeer pid
  pure (stored,queued)

def dropWrite (pid : PeerId) (read : Peer × Peer) : WG.M Unit :=
  setPeer pid {read.1 with txQueue := read.2.txQueue.dropPeeked}

theorem drop_factor (pid : PeerId) : txDropSource pid=dropRead pid >>= dropWrite pid := by
  simp only [txDropSource,dropRead,dropWrite,bind_assoc,pure_bind]

/-- A reached native read prefix carries the original fixed setter remainder. -/
theorem drop_continuation {read : Peer × Peer}
    (reached : ((dropRead pid).run w).run a=.ok ((read,v),b)) :
    ((txDropSource pid).run w).run a=((dropWrite pid read).run v).run b := by
  rw [drop_factor]
  simp only [StateT.run_bind,reached]
  rfl

/-- The actual queue choice and second peer read determine the remaining write. -/
theorem peek_continuation {read : (Option (List SkbId) × PrevQueue (List SkbId)) × Peer}
    (reached : ((peekRead pid).run w).run a=.ok ((read,v),b)) :
    ((txPeekSource pid).run w).run a=((peekTail pid read).run v).run b := by
  rw [peek_factor]
  simp only [StateT.run_bind,reached]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
