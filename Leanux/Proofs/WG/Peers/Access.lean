import Leanux.Proofs.WG.Peers.Frames
import Leanux.Proofs.WG.Lifetimes.Events
import Leanux.Proofs.Logged.Prefix
import Leanux.WG.NetlinkDump
import Leanux.Proofs.WG.Keypairs.Frames.WGMore

set_option pp.structureInstances false
set_option maxHeartbeats 1000000

/-! Source-level peer-access observation of the original release helper and
dump-completion callback. The resolved getter inside peerPut is explicit, including
the current source getters. Errors retain the prefix already observed. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

abbrev PeerEvent := AccessEvent PeerId Nat

def getPeerPrefix (pid : PeerId) : PrefixM PeerEvent Peer :=
  fun w => ExceptT.mk fun h => match (getPeer pid).run w with
    | .error e => (.error e, h)
    | .ok (p, v) => (.ok (p, v), h ++ [.read pid p.internalId])

/-- An absent device makes the original setter a no-op, so it emits no write.
An insertion into an absent slot of a present device is still a write. -/
def setPeerPrefix (pid : PeerId) (p : Peer) : PrefixM PeerEvent Unit :=
  fun w => ExceptT.mk fun h => ((setPeer pid p).run w,
    if w.k.wg.isSome then h ++ [.write pid p.internalId] else h)

/-- The actual inline release update, including its dropped-packet counter.
The event names exactly the resident removed by that update, if any. -/
def erasePeerPrefix (pid : PeerId) (dropped : Nat) : PrefixM PeerEvent Unit :=
  fun w => ExceptT.mk fun h =>
    ((modifyDev fun d => { d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid }).run w,
      match (snapshot w).slots pid with
      | none => h
      | some stamp => h ++ [.release pid stamp])

def requireNotPendingPrefix (_pid : PeerId) (_what : String) : PrefixM PeerEvent Unit := pure ()

def peerPutPrefix (peer : Option PeerId) : PrefixM PeerEvent Unit := do
  if ← liftPrefix (branch .peerPutNull peer.isNone) then return
  let some pid := peer | liftPrefix (invariant "unreachable")
  requireNotPendingPrefix pid "a reference count the handshake worker also changes"
  let p ← getPeerPrefix pid
  setPeerPrefix pid { p with refcount := p.refcount - 1 }
  if ← liftPrefix (branch .peerKrefPutReleased (← liftPrefix (refcountDecAndTest p.refcount))) then
    liftPrefix (indexRemove pid .handshake)
    erasePeerPrefix pid p.staged.length
    liftPrefix (retirePeerUnits pid)

def wgGetDeviceDonePrefix (ctx : DumpCtx) : PrefixM PeerEvent Unit := do
  let _ ← liftPrefix (branch .getDoneHasWg ctx.hasWg)
  peerPutPrefix ctx.nextPeer

@[simp] theorem getPeerPrefix_run (pid : PeerId) (w : World) (h : List PeerEvent) :
    runPrefix (getPeerPrefix pid) w h = match (getPeer pid).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.read pid p.internalId]) := rfl

@[simp] theorem setPeerPrefix_run (pid : PeerId) (p : Peer) (w : World) (h : List PeerEvent) :
    runPrefix (setPeerPrefix pid p) w h = ((setPeer pid p).run w,
      if w.k.wg.isSome then h ++ [.write pid p.internalId] else h) := rfl

@[simp] theorem erasePeerPrefix_run (pid : PeerId) (n : Nat) (w : World) (h : List PeerEvent) :
    runPrefix (erasePeerPrefix pid n) w h =
      ((modifyDev fun d => { d with txDropped := d.txDropped + n, peers := d.peers.erase pid }).run w,
        match (snapshot w).slots pid with
        | none => h
        | some stamp => h ++ [.release pid stamp]) := rfl

theorem getPeerPrefix_erases (pid : PeerId) : ErasesPrefix (getPeerPrefix pid) (getPeer pid) := by
  intro w h
  simp only [getPeerPrefix, runPrefix, StateT.run, ExceptT.run, ExceptT.mk]
  cases (getPeer pid) w <;> rfl

theorem setPeerPrefix_erases (pid : PeerId) (p : Peer) :
    ErasesPrefix (setPeerPrefix pid p) (setPeer pid p) := fun _ _ => rfl

theorem erasePeerPrefix_erases (pid : PeerId) (dropped : Nat) :
    ErasesPrefix (erasePeerPrefix pid dropped)
      (modifyDev fun d => { d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid }) := fun _ _ => rfl

theorem requireNotPendingPrefix_erases (pid : PeerId) (what : String) :
    ErasesPrefix (requireNotPendingPrefix pid what) (requireNotPending pid what) := by
  exact erasesPrefix_pure _

theorem peerPutPrefix_erases (peer : Option PeerId) :
    ErasesPrefix (peerPutPrefix peer) (peerPut peer) := by
  unfold peerPutPrefix peerPut
  repeat' first
    | rfl
    | contradiction
    | apply erasesPrefix_bind
    | exact getPeerPrefix_erases _
    | exact setPeerPrefix_erases _ _
    | exact erasePeerPrefix_erases _ _
    | exact requireNotPendingPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | intro x
    | split
  all_goals simp_all [runPrefix_pure, runPrefix_lift]

theorem wgGetDeviceDonePrefix_erases (ctx : DumpCtx) :
    ErasesPrefix (wgGetDeviceDonePrefix ctx) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDonePrefix wgGetDeviceDone
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => peerPutPrefix_erases _)

/-- Complete expected observations, including errors. A count of zero writes
the resident before refcountDecAndTest rejects it; No failed getter resolves an object. -/
def peerPutEvents (peer : Option PeerId) (w : World) : List PeerEvent :=
  match peer with
  | none => []
  | some pid => match w.k.wg.bind (fun d => d.peers[pid]?) with
    | none => []
    | some p =>
      [.read pid p.internalId, .write pid p.internalId] ++
        if p.refcount = 1 then [.release pid p.internalId] else []

theorem peerPutPrefix_events (peer : Option PeerId) (w : World) (h : List PeerEvent) :
    (runPrefix (peerPutPrefix peer) w h).2 = h ++ peerPutEvents peer w := by
  cases peer with
  | none => simp [peerPutPrefix, peerPutEvents, runPrefix_bind, branch, StateT.run_bind,
      StateT.run_modify, StateT.run_pure]
  | some pid =>
    cases hd : w.k.wg with
    | none => simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
        runPrefix_bind, getPeer, getDev, getK, hd, branch, invariant]
    | some d =>
      cases hp : d.peers[pid]? with
      | none => simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
          runPrefix_bind, getPeer, getDev, getK, hd, hp, branch, invariant]
      | some p =>
        by_cases hz : p.refcount = 0
        · simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
            runPrefix_bind, getPeer, getDev, getK, hd, hp, hz, setPeer, modifyDev,
            modifyK, refcountDecAndTest, branch, branchCmp, invariant, unsupported, List.append_assoc]
        · have hpos : 0 < p.refcount := Nat.pos_of_ne_zero hz
          by_cases ho : p.refcount = 1
          all_goals simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
            runPrefix_bind, getPeer, getDev, getK, hd, hp, hz, ho, hpos, setPeer,
            modifyDev, modifyK, refcountDecAndTest, branch, branchCmp, invariant,
            indexRemove_eq, indexUnhash, retirePeerUnits, snapshot,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_get,
            Std.TreeMap.getElem?_insert, List.append_assoc]

/-- Erasure and exact source observation together, for every input including
missing objects and invalid reference counts. -/
theorem peerPutPrefix_run (peer : Option PeerId) (w : World) (h : List PeerEvent) :
    runPrefix (peerPutPrefix peer) w h =
      ((peerPut peer).run w, h ++ peerPutEvents peer w) :=
  Prod.ext (peerPutPrefix_erases peer w h) (peerPutPrefix_events peer w h)

theorem wgGetDeviceDonePrefix_run (ctx : DumpCtx) (w : World) (h : List PeerEvent) :
    runPrefix (wgGetDeviceDonePrefix ctx) w h =
      ((wgGetDeviceDone ctx).run w, h ++ peerPutEvents ctx.nextPeer w) := by
  apply Prod.ext (wgGetDeviceDonePrefix_erases ctx w h)
  simp only [wgGetDeviceDonePrefix, runPrefix_bind, runPrefix_lift]
  simp [branch, StateT.run_bind, StateT.run_modify, StateT.run_pure,
    peerPutPrefix_events, peerPutEvents]

/-- No frontier bound is needed: this component allocates no identities. -/
def AccessInv (h : List PeerEvent) (w : World) : Prop :=
  AccessEvent.Safe h ∧ Unique (snapshot w) ∧
    ∀ stamp, AccessEvent.Released h stamp → Absent (snapshot w) stamp

theorem peerPutEvents_safe (peer : Option PeerId) (w : World) (h : List PeerEvent)
    (hi : AccessInv h w) : AccessEvent.Safe (h ++ peerPutEvents peer w) := by
  cases peer with
  | none => simpa [peerPutEvents] using hi.1
  | some pid =>
    cases hp : w.k.wg.bind (fun d => d.peers[pid]?) with
    | none => simpa [peerPutEvents, hp] using hi.1
    | some p =>
      have live : (snapshot w).slots pid = some p.internalId := by
        change (w.k.wg.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
        rw [hp]; rfl
      have hn : ¬ AccessEvent.Released h p.internalId := fun hr => hi.2.2 _ hr pid live
      have one := AccessEvent.safe_append_read (slot := pid) (stamp := p.internalId) hi.1 hn
      have two := AccessEvent.safe_append_write (slot := pid) (stamp := p.internalId) one
        (by simpa only [AccessEvent.released_append_read] using hn)
      by_cases released : p.refcount = 1
      · have three := AccessEvent.safe_append_release (slot := pid) (stamp := p.internalId) two
        simpa [peerPutEvents, hp, released, List.append_assoc] using three
      · simpa [peerPutEvents, hp, released, List.append_assoc] using two

theorem peerPutEvents_release (peer : Option PeerId) (w : World) (stamp : Nat)
    (hr : AccessEvent.Released (peerPutEvents peer w) stamp) :
    ∃ pid p, peer = some pid ∧ w.k.wg.bind (fun d => d.peers[pid]?) = some p ∧
      p.refcount = 1 ∧ stamp = p.internalId := by
  cases peer with
  | none => simp [peerPutEvents, AccessEvent.Released] at hr
  | some pid =>
    cases hp : w.k.wg.bind (fun d => d.peers[pid]?) with
    | none => simp [peerPutEvents, hp, AccessEvent.Released] at hr
    | some p =>
      by_cases released : p.refcount = 1
      · refine ⟨pid, p, rfl, hp, released, ?_⟩
        simpa [peerPutEvents, hp, released, AccessEvent.Released] using hr
      · simp [peerPutEvents, hp, released, AccessEvent.Released] at hr

theorem peerPut_release_snapshot (pid : PeerId) (w w' : World) (p : Peer)
    (hp : w.k.wg.bind (fun d => d.peers[pid]?) = some p) (hc : p.refcount = 1)
    (hr : (peerPut (some pid)).run w = .ok ((), w')) :
    snapshot w' = (snapshot w).put pid none := by
  cases hd : w.k.wg with
  | none => simp [hd] at hp
  | some d =>
    simp only [hd, Option.bind_some] at hp
    simp [peerPut, requireNotPending, getPeer, getDev, getK, hd, hp, hc,
      setPeer, modifyDev, modifyK, refcountDecAndTest, branch, branchCmp,
      indexRemove_eq, indexUnhash, retirePeerUnits, StateT.run_bind, StateT.run_modify,
      StateT.run_pure, StateT.run_get] at hr
    cases hr
    apply Store.ext
    · rfl
    · funext j
      by_cases hj : pid = j
      · subst j
        simp [snapshot, hd, Store.put, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]
      · simp [snapshot, hd, Store.put, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
          Std.LawfulEqOrd.compare_eq_iff_eq, hj, Ne.symm hj]

theorem peerPutPrefix_preserves (peer : Option PeerId) :
    PrefixPreserves AccessInv AccessEvent.Safe (peerPutPrefix peer) := by
  intro w h hi
  rw [peerPutPrefix_run]
  refine ⟨peerPutEvents peer w, rfl, peerPutEvents_safe peer w h hi, ?_⟩
  cases hr : (peerPut peer).run w with
  | error _ => trivial
  | ok out =>
    rcases out with ⟨result, w'⟩
    cases result
    have retained := peerPut_retained peer w () w' hr
    refine ⟨peerPutEvents_safe peer w h hi, retained.unique hi.2.1, ?_⟩
    intro stamp released
    rcases AccessEvent.released_append.mp released with old | new
    · exact retained.absent (hi.2.2 _ old)
    · obtain ⟨pid, p, rfl, hp, hc, rfl⟩ := peerPutEvents_release peer w stamp new
      rw [peerPut_release_snapshot pid w w' p hp hc hr]
      apply hi.2.1.erase_absent
      change (w.k.wg.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
      rw [hp]; rfl

theorem wgGetDeviceDonePrefix_preserves (ctx : DumpCtx) :
    PrefixPreserves AccessInv AccessEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  unfold wgGetDeviceDonePrefix
  apply PrefixPreserves.bind (g := liftPrefix (branch .getDoneHasWg ctx.hasWg))
  · intro w h hi
    refine ⟨[], ?_, hi.1, ?_⟩
    · simp
    · simpa [branch, StateT.run_bind, StateT.run_modify, StateT.run_pure, AccessInv, snapshot]
        using hi
  · intro _
    exact peerPutPrefix_preserves _

/-- This finite family contains only the complete original release helper and
its dump-completion caller; it does not stand for arbitrary syscalls. -/
inductive AccessCall where
  | put (peer : Option PeerId)
  | dumpDone (ctx : DumpCtx)

namespace AccessCall

def original : AccessCall → M Unit
  | .put peer => peerPut peer
  | .dumpDone ctx => wgGetDeviceDone ctx

def observed : AccessCall → PrefixM PeerEvent Unit
  | .put peer => peerPutPrefix peer
  | .dumpDone ctx => wgGetDeviceDonePrefix ctx

def execute : List AccessCall → M Unit
  | [] => pure ()
  | call :: calls => call.original >>= fun _ => execute calls

def observe : List AccessCall → PrefixM PeerEvent Unit
  | [] => pure ()
  | call :: calls => call.observed >>= fun _ => observe calls

theorem erases (call : AccessCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | put peer => exact peerPutPrefix_erases peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_erases ctx

theorem preserves (call : AccessCall) : PrefixPreserves AccessInv AccessEvent.Safe call.observed := by
  cases call with
  | put peer => exact peerPutPrefix_preserves peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_preserves ctx

theorem observe_erases (calls : List AccessCall) : ErasesPrefix (observe calls) (execute calls) := by
  induction calls with
  | nil => exact erasesPrefix_pure ()
  | cons call calls ih => exact erasesPrefix_bind call.erases (fun _ => ih)

theorem observe_preserves (calls : List AccessCall) :
    PrefixPreserves AccessInv AccessEvent.Safe (observe calls) := by
  induction calls with
  | nil => exact PrefixPreserves.pure (fun _ _ h => h.1) ()
  | cons call calls ih => exact PrefixPreserves.bind call.preserves (fun _ => ih)

end AccessCall
end Leanux.Proofs.WG.Peers
