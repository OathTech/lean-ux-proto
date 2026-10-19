import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontPath
import Leanux.Proofs.WG.TransmitSecurity.StagedTrim

/-! Fixed native residual prefixes. The overflow loop retains its finite
source bound and early break; each successful iteration has two separate
writes, queue removal followed by its counter charge. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity CausalJournal
set_option maxHeartbeats 600000

def gate (pid : PeerId) : WG.M (Peer × Bool) := do
  let p ← getPeer pid
  let excess ← branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS)
  pure (p,excess)

def drop (pid : PeerId) (p : Peer) : WG.M Unit :=
  setPeer pid {p with staged := p.staged.drop 1}

def charge : WG.M Unit := modifyDev fun d => {d with txDropped := d.txDropped+1}

theorem body_factor (pid : PeerId) : Staged.trimBody pid = (do
    let (p,excess) ← gate pid
    if excess then drop pid p; charge; pure (.yield ()) else pure (.done ())) := by
  simp only [Staged.trimBody,gate,drop,charge,bind_assoc,pure_bind]

def trimPrefix (pid : PeerId) : Nat → WG.M (ForInStep Unit)
  | 0 => pure (.yield ())
  | n+1 => do
      match ← Staged.trimBody pid with
      | .done _ => pure (.done ())
      | .yield _ => trimPrefix pid n

def finish : ForInStep Unit → WG.M Unit := fun _ => pure ()

theorem prefix_add (pid : PeerId) (n m : Nat) :
    trimPrefix pid (n+m) = (do
      match ← trimPrefix pid n with
      | .done _ => pure (.done ())
      | .yield _ => trimPrefix pid m) := by
  induction n with
  | zero => simp only [Nat.zero_add,trimPrefix,pure_bind]
  | succ n ih =>
    simp only [Nat.succ_add,trimPrefix,ih,bind_assoc]
    congr 1
    funext result
    cases result <;> simp only [pure_bind]

/-- This loop is the original finite range loop, not an arbitrary action
factor selected retrospectively from a failure. -/
theorem list_loop (pid : PeerId) (indices : List Nat) :
    (forIn indices () (fun _ _ => Staged.trimBody pid) : WG.M Unit) =
      (trimPrefix pid indices.length >>= finish) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    simp only [List.forIn_cons,List.length_cons,trimPrefix,bind_assoc,ih]
    congr 1
    funext result
    cases result <;> rfl

theorem trim_factor (pid : PeerId) : xmitTrim pid = (do
    let p ← getPeer pid
    let _ ← trimPrefix pid (p.staged.length+1)
    pure ()) := by
  unfold xmitTrim
  congr 1
  funext p
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn (List.range' 0 (p.staged.length+1) 1) () (fun _ _ => Staged.trimBody pid) >>= fun _ => pure ()) = _
  rw [list_loop]
  simp only [List.length_range',bind_assoc,finish,pure_bind]

/-- Literal initial read followed by the first n iterations of that bound. -/
def trimTo (pid : PeerId) (n : Nat) : WG.M (ForInStep Unit) := do
  let _ ← getPeer pid
  trimPrefix pid n

/-- Literal source prefix ending between drop and charge in iteration n. -/
def dropTo (pid : PeerId) (n : Nat) : WG.M (Option Peer) := do
  match ← trimTo pid n with
  | .done _ => pure none
  | .yield _ =>
    let (peer,accepted) ← gate pid
    if accepted then
      drop pid peer
      pure (some peer)
    else pure none

/-- The actual silent write after both native splice reads. -/
def splicePrefix (pid : PeerId) (packets : List Packet) : WG.M Unit := do
  let first ← getPeer pid
  let second ← getPeer pid
  setPeer pid {first with staged := second.staged ++ packets}

theorem splice_factor (pid : PeerId) (packets : List Packet) :
    xmitSplice pid packets = splicePrefix pid packets := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
