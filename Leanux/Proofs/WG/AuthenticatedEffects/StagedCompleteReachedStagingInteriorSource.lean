import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteKeepalive

/-! Fixed native prefixes at the staged queue writes. These definitions keep
the original read and choice order; only the existing completed receipts
separate native mutations from ledger transfer or admission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

def takeRead (pid : PeerId) : WG.M (Peer × Bool) := do
  let peer ← getPeer pid
  let empty ← branch .stagedEmpty peer.staged.isEmpty
  pure (peer,empty)

def takeWrite (pid : PeerId) (peer : Peer) : WG.M Unit :=
  setPeer pid {peer with staged := []}

def takeTail (pid : PeerId) (read : Peer × Bool) : WG.M (Option Peer) := do
  if read.2 then return none
  takeWrite pid read.1
  pure (some read.1)

theorem take_factor (pid : PeerId) : Take.takePrefix pid=takeRead pid >>= takeTail pid := by
  simp only [Take.takePrefix,takeRead,takeTail,takeWrite,bind_assoc,pure_bind]

def restoreRead (pid : PeerId) : WG.M (Peer × Peer) := do
  let cached ← getPeer pid
  let queued ← getPeer pid
  pure (cached,queued)

def restoreWrite (pid : PeerId) (packets : List Packet) (read : Peer × Peer) : WG.M Unit :=
  setPeer pid {read.1 with staged := packets++read.2.staged}

theorem restore_factor (pid : PeerId) (packets : List Packet) :
    Restore.nativeRestore pid packets=restoreRead pid >>= restoreWrite pid packets := by
  simp only [Restore.nativeRestore,restoreRead,restoreWrite,bind_assoc,pure_bind]

def keepaliveRead (pid : PeerId) : WG.M (Peer × Bool) := do
  let peer ← getPeer pid
  let empty ← branch .keepaliveStagedEmpty peer.staged.isEmpty
  pure (peer,empty)

/-- Allocation and its refusal branch are the actual ambient source child. -/
def keepaliveAllocation : AmbientM Bool := do
  let allocated ← AmbientM.hiddenAlloc .keepaliveSkb
  AmbientM.branch .keepaliveNoMem (!allocated)

def keepaliveAllocate : WG.M Bool := do
  let allocated ← hiddenAlloc .keepaliveSkb
  branch .keepaliveNoMem (!allocated)

def keepaliveMtu : WG.M Nat := do pure (←getDev).mtu

def keepaliveWrite (pid : PeerId) (peer : Peer) (mtu : Nat) : WG.M Unit :=
  setPeer pid {peer with staged := peer.staged++[{mtu}]}

def keepaliveInsert (pid : PeerId) (peer : Peer) : WG.M Bool := do
  let mtu ← keepaliveMtu
  keepaliveWrite pid peer mtu
  pure true

def keepaliveTail (pid : PeerId) (read : Peer × Bool) : WG.M Bool := do
  if read.2 then
    if ← keepaliveAllocate then return false
    keepaliveInsert pid read.1
  else pure true

theorem keepalive_factor (pid : PeerId) :
    RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid=
      keepaliveRead pid >>= keepaliveTail pid := by
  simp only [RetirementSecurity.OccurrenceHandshake.keepalivePrepare,keepaliveRead,
    keepaliveTail,keepaliveAllocate,keepaliveInsert,keepaliveMtu,keepaliveWrite,bind_assoc,pure_bind]
/-- This prefix ends after the literal allocation outcome, before the MTU
read or insertion. The original tail still selects refusal versus insertion. -/
def keepaliveAllocated (pid : PeerId) : WG.M (Peer × Option Bool) := do
  let read ← keepaliveRead pid
  if read.2 then
    let refused ← keepaliveAllocate
    pure (read.1,some refused)
  else pure (read.1,none)

def keepaliveRemaining (pid : PeerId) (read : Peer × Option Bool) : WG.M Bool :=
  match read.2 with
  | none => pure true
  | some true => pure false
  | some false => keepaliveInsert pid read.1

theorem keepalive_allocated_factor (pid : PeerId) :
    RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid=
      keepaliveAllocated pid >>= keepaliveRemaining pid := by
  rw [keepalive_factor]
  simp only [keepaliveAllocated,bind_assoc]
  congr 1
  funext read
  obtain ⟨peer,empty⟩:=read
  cases empty <;> simp only [keepaliveTail,Bool.false_eq_true,ite_false,ite_true,pure_bind,keepaliveRemaining,bind_assoc]
  congr 1
  funext refused
  cases refused <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
