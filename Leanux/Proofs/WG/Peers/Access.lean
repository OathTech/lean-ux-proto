import Leanux.Proofs.WG.Peers.Frames
import Leanux.Proofs.WG.Lifetimes.Events
import Leanux.Proofs.Logged.WGPrefix
import Leanux.WG.NetlinkDump
import Leanux.Proofs.Framing.Index

set_option pp.structureInstances false
set_option maxHeartbeats 1000000

/-! Source-level peer-access observation of the original release helper and
dump-completion callback. The resolved getter inside peerPut is explicit, including
the current source getters. Errors retain the prefix already observed. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

abbrev PeerEvent := AccessEvent PeerId Nat

def getPeerPrefix (pid : PeerId) : WGPrefix PeerEvent Peer :=
  fun w ambient => ExceptT.mk fun h => match ((getPeer pid).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((p, v), ambient') => (.ok ((p, v), ambient'), h ++ [.read pid p.internalId])

/-- An absent device makes the original setter a no-op, so it emits no write.
An insertion into an absent slot of a present device is still a write. -/
def setPeerPrefix (pid : PeerId) (p : Peer) : WGPrefix PeerEvent Unit :=
  fun w ambient => ExceptT.mk fun h => (((setPeer pid p).run w).run ambient,
    if w.dev.isSome then h ++ [.write pid p.internalId] else h)

/-- The actual inline release update, including its dropped-packet counter.
The event names exactly the resident removed by that update, if any. -/
def erasePeerPrefix (pid : PeerId) (dropped : Nat) : WGPrefix PeerEvent Unit :=
  fun w ambient => ExceptT.mk fun h =>
    (((modifyDev fun d => { d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid }).run w).run ambient,
      match (snapshot w).slots pid with
      | none => h
      | some stamp => h ++ [.release pid stamp])

def requireNotPendingPrefix (_pid : PeerId) (_what : String) : WGPrefix PeerEvent Unit := pure ()

def peerPutPrefix (peer : Option PeerId) : WGPrefix PeerEvent Unit := do
  if ← liftWGPrefix (branch .peerPutNull peer.isNone) then return
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  requireNotPendingPrefix pid "a reference count the handshake worker also changes"
  let p ← getPeerPrefix pid
  setPeerPrefix pid { p with refcount := p.refcount - 1 }
  if ← liftWGPrefix (branch .peerKrefPutReleased (← liftWGPrefix (refcountDecAndTest p.refcount))) then
    liftWGPrefix (liftIndex (indexRemove (.handshake pid)))
    if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
      liftWGPrefix (invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
    erasePeerPrefix pid p.staged.length
    if let some t := PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome) then
      liftWGPrefix (invariant s!"peer {pid} released with its {repr t} timer pending")
    liftWGPrefix (retirePeerUnits pid)

def wgGetDeviceDonePrefix (ctx : DumpCtx) : WGPrefix PeerEvent Unit := do
  let _ ← liftWGPrefix (branch .getDoneHasWg ctx.hasWg)
  peerPutPrefix ctx.nextPeer

@[simp] theorem getPeerPrefix_run (pid : PeerId) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (getPeerPrefix pid) w ambient h = match ((getPeer pid).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((p, v), ambient') => (.ok ((p, v), ambient'), h ++ [.read pid p.internalId]) := rfl

@[simp] theorem setPeerPrefix_run (pid : PeerId) (p : Peer) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (setPeerPrefix pid p) w ambient h = (((setPeer pid p).run w).run ambient,
      if w.dev.isSome then h ++ [.write pid p.internalId] else h) := rfl

@[simp] theorem erasePeerPrefix_run (pid : PeerId) (n : Nat) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (erasePeerPrefix pid n) w ambient h =
      (((modifyDev fun d => { d with txDropped := d.txDropped + n, peers := d.peers.erase pid }).run w).run ambient,
        match (snapshot w).slots pid with
        | none => h
        | some stamp => h ++ [.release pid stamp]) := rfl

theorem getPeerPrefix_erases (pid : PeerId) : ErasesStatePrefix (getPeerPrefix pid) (getPeer pid) := by
  intro w ambient h
  simp only [getPeerPrefix, runPrefix, StateT.run, ExceptT.run, ExceptT.mk]
  cases (getPeer pid) w ambient <;> rfl

theorem setPeerPrefix_erases (pid : PeerId) (p : Peer) :
    ErasesStatePrefix (setPeerPrefix pid p) (setPeer pid p) := fun _ _ _ => rfl

theorem erasePeerPrefix_erases (pid : PeerId) (dropped : Nat) :
    ErasesStatePrefix (erasePeerPrefix pid dropped)
      (modifyDev fun d => { d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid }) := fun _ _ _ => rfl

theorem requireNotPendingPrefix_erases (pid : PeerId) (what : String) :
    ErasesStatePrefix (requireNotPendingPrefix pid what) (requireNotPending pid what) := by
  exact erasesStatePrefix_pure _

theorem peerPutPrefix_erases (peer : Option PeerId) :
    ErasesStatePrefix (peerPutPrefix peer) (peerPut peer) := by
  unfold peerPutPrefix peerPut
  repeat' first
    | rfl
    | contradiction
    | apply erasesStatePrefix_bind
    | exact getPeerPrefix_erases _
    | exact setPeerPrefix_erases _ _
    | exact erasePeerPrefix_erases _ _
    | exact requireNotPendingPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | intro x
    | split
  all_goals simp_all [liftWGPrefix, liftStatePrefix, StateT.run, runPrefix_lift, runPrefix_pure]
  all_goals rfl

theorem wgGetDeviceDonePrefix_erases (ctx : DumpCtx) :
    ErasesStatePrefix (wgGetDeviceDonePrefix ctx) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDonePrefix wgGetDeviceDone
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => peerPutPrefix_erases _)

/-- Complete expected observations, including errors. A count of zero writes
the resident before refcountDecAndTest rejects it; No failed getter resolves an object. -/
def peerPutEvents (peer : Option PeerId) (w : WGWorld) : List PeerEvent :=
  match peer with
  | none => []
  | some pid => match w.dev.bind (fun d => d.peers[pid]?) with
    | none => []
    | some p =>
      [.read pid p.internalId, .write pid p.internalId] ++
        if p.refcount = 1 ∧
          (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = false
        then [.release pid p.internalId] else []

theorem peerPutPrefix_events (peer : Option PeerId) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    (runStatePrefix (peerPutPrefix peer) w ambient h).2 = h ++ peerPutEvents peer w := by
  cases peer with
  | none =>
    simp [peerPutPrefix, peerPutEvents, runStatePrefix_bind, liftWGPrefix,
      branch, AmbientM.branch, StateT.run_bind, StateT.run_modify, StateT.run_pure] <;> rfl
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
        runStatePrefix_bind, liftWGPrefix, getPeer, getDev, hd,
        branch, AmbientM.branch, invariant, AmbientM.invariant,
        StateT.run_bind, StateT.run_modify, StateT.run_pure] <;> rfl
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
          runStatePrefix_bind, liftWGPrefix, getPeer, getDev, hd, hp,
          branch, AmbientM.branch, invariant, AmbientM.invariant,
          StateT.run_bind, StateT.run_modify, StateT.run_pure] <;> rfl
      | some p =>
        by_cases hz : p.refcount = 0
        · simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
            runStatePrefix_bind, liftWGPrefix, getPeer, getDev, hd, hp, hz,
            setPeer, modifyDev, refcountDecAndTest, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp, invariant, unsupported,
            AmbientM.invariant, AmbientM.unsupported,
            StateT.run_bind, StateT.run_modify, StateT.run_pure, List.append_assoc] <;> rfl
        · have hpos : 0 < p.refcount := Nat.pos_of_ne_zero hz
          by_cases ho : p.refcount = 1
          all_goals
            cases hq : p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty
            <;> simp at hq
            <;> cases ht : PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome)
            <;> simp [peerPutPrefix, peerPutEvents, requireNotPendingPrefix,
              runStatePrefix_bind, liftWGPrefix, getPeer, getDev, hd, hp, hz, ho, hpos,
              hq, ht, setPeer, modifyDev, refcountDecAndTest, branch, branchCmp,
              AmbientM.branch, AmbientM.branchCmp, invariant, unsupported,
              AmbientM.invariant, AmbientM.unsupported, indexRemove_eq, indexUnhash,
              liftIndex, retirePeerUnits, modifyAmbient, snapshot,
              StateT.run_bind, StateT.run_modify, StateT.run_pure, StateT.run_get,
              Std.TreeMap.getElem?_insert, List.append_assoc]
            <;> first
            | rfl
            | have hempty : ¬ (((p.txQueue.peeked = none ∧ p.txQueue.items = []) ∧
                  p.rxQueue.peeked = none) ∧ p.rxQueue.items = []) := by
                intro he
                rcases he with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
                simp_all
              simp only [ite_eq_right hempty]
              rfl

/-- Erasure and exact source observation together, for every input including
missing objects and invalid reference counts. -/
theorem peerPutPrefix_run (peer : Option PeerId) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (peerPutPrefix peer) w ambient h =
      (((peerPut peer).run w).run ambient, h ++ peerPutEvents peer w) :=
  Prod.ext (peerPutPrefix_erases peer w ambient h) (peerPutPrefix_events peer w ambient h)

theorem wgGetDeviceDonePrefix_run (ctx : DumpCtx) (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (wgGetDeviceDonePrefix ctx) w ambient h =
      (((wgGetDeviceDone ctx).run w).run ambient, h ++ peerPutEvents ctx.nextPeer w) := by
  apply Prod.ext (wgGetDeviceDonePrefix_erases ctx w ambient h)
  change (runStatePrefix
    (liftWGPrefix (branch .getDoneHasWg ctx.hasWg) >>= fun _ => peerPutPrefix ctx.nextPeer)
    w ambient h).2 = _
  rw [runStatePrefix_bind]
  change (runStatePrefix (peerPutPrefix ctx.nextPeer) w
    { ambient with steps := ambient.steps.push { decision := .getDoneHasWg, outcome := ctx.hasWg, netRx := ambient.netRxSection } } h).2 = _
  exact peerPutPrefix_events ctx.nextPeer w _ h

/-- No frontier bound is needed: this component allocates no identities. -/
def AccessInv (h : List PeerEvent) (w : WGWorld) : Prop :=
  AccessEvent.Safe h ∧ Unique (snapshot w) ∧
    ∀ stamp, AccessEvent.Released h stamp → Absent (snapshot w) stamp

theorem peerPutEvents_safe (peer : Option PeerId) (w : WGWorld) (h : List PeerEvent)
    (hi : AccessInv h w) : AccessEvent.Safe (h ++ peerPutEvents peer w) := by
  cases peer with
  | none => simpa [peerPutEvents] using hi.1
  | some pid =>
    cases hp : w.dev.bind (fun d => d.peers[pid]?) with
    | none => simpa [peerPutEvents, hp] using hi.1
    | some p =>
      have live : (snapshot w).slots pid = some p.internalId := by
        change (w.dev.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
        rw [hp]; rfl
      have hn : ¬ AccessEvent.Released h p.internalId := fun hr => hi.2.2 _ hr pid live
      have one := AccessEvent.safe_append_read (slot := pid) (stamp := p.internalId) hi.1 hn
      have two := AccessEvent.safe_append_write (slot := pid) (stamp := p.internalId) one
        (by simpa only [AccessEvent.released_append_read] using hn)
      by_cases released : p.refcount = 1 ∧
        (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = false
      · have three := AccessEvent.safe_append_release (slot := pid) (stamp := p.internalId) two
        simp only [peerPutEvents, hp]
        rw [ite_eq_left released]
        simpa [List.append_assoc] using three
      · simp only [peerPutEvents, hp]
        rw [ite_eq_right released]
        simpa [List.append_assoc] using two

theorem peerPutEvents_release (peer : Option PeerId) (w : WGWorld) (stamp : Nat)
    (hr : AccessEvent.Released (peerPutEvents peer w) stamp) :
    ∃ pid p, peer = some pid ∧ w.dev.bind (fun d => d.peers[pid]?) = some p ∧
      p.refcount = 1 ∧ stamp = p.internalId := by
  cases peer with
  | none => simp [peerPutEvents, AccessEvent.Released] at hr
  | some pid =>
    cases hp : w.dev.bind (fun d => d.peers[pid]?) with
    | none => simp [peerPutEvents, hp, AccessEvent.Released] at hr
    | some p =>
      by_cases released : p.refcount = 1 ∧
        (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty || p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = false
      · refine ⟨pid, p, rfl, hp, released.1, ?_⟩
        simp only [peerPutEvents, hp, ite_eq_left released] at hr
        simpa [AccessEvent.Released] using hr
      · simp only [peerPutEvents, hp, ite_eq_right released] at hr
        simp [AccessEvent.Released] at hr

theorem peerPut_release_snapshot (pid : PeerId) (w w' : WGWorld) (ambient ambient' : Ambient) (p : Peer)
    (hp : w.dev.bind (fun d => d.peers[pid]?) = some p) (hc : p.refcount = 1)
    (hr : ((peerPut (some pid)).run w).run ambient = .ok (((), w'), ambient')) :
    snapshot w' = (snapshot w).put pid none := by
  have full : Hoare (peerPut (some pid)) (fun g => g = w)
      (fun _ g => snapshot g = (snapshot w).put pid none) := by
    clear hr w' ambient ambient'
    obtain ⟨d, hd, hp⟩ := Option.bind_eq_some_iff.mp hp
    have unhash (a : IndexM Unit) (g : WGWorld) : Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => w = g)
        (fun _ w => ∃ table, w = {g with dev := g.dev.map fun d => {d with indexTable := table}}) := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient x w' ambient' hw hr
      subst w
      change ((liftIndex a).run g).run ambient = .ok ((x, w'), ambient') at hr
      rw [liftIndex_run] at hr
      cases hg : g.dev with
      | none => simp [hg] at hr
      | some d =>
        simp only [hg] at hr
        cases ha : (a.run d.indexTable).run ambient with
        | error e => simp [ha, Except.map] at hr
        | ok out =>
          rcases out with ⟨⟨y, table⟩, ambient''⟩
          simp only [ha, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
          rcases hr with ⟨⟨_, hw⟩, _⟩
          exact ⟨table, by simpa [hg] using hw.symm⟩
    unfold Hoare at unhash ⊢
    mvcgen [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
      branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
      refcountDecAndTest, unhash, retirePeerUnits, modifyAmbient,
      unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals try obtain ⟨table, rfl⟩ := ‹∃ table, _ = _›
    all_goals subst_vars
    all_goals simp_all
    all_goals apply Store.ext
    all_goals first
    | rfl
    | (funext j
       by_cases hj : pid = j
       · subst j
         simp_all [snapshot, Store.put, Std.TreeMap.getElem?_erase,
           Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
       · simp_all [snapshot, Store.put, Std.TreeMap.getElem?_erase,
           Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq, Ne.symm hj])
  exact (hoare_iff_run_ambient _ _ _).mp full w ambient () w' ambient' rfl hr

theorem peerPutPrefix_preserves (peer : Option PeerId) :
    StatePrefixPreserves (fun h w _ => AccessInv h w) AccessEvent.Safe (peerPutPrefix peer) := by
  intro w ambient h hi
  have he : runPrefix ((peerPutPrefix peer).run w) ambient h =
      (((peerPut peer).run w).run ambient, h ++ peerPutEvents peer w) :=
    peerPutPrefix_run peer w ambient h
  rw [he]
  refine ⟨peerPutEvents peer w, rfl, peerPutEvents_safe peer w h hi, ?_⟩
  cases hr : ((peerPut peer).run w).run ambient with
  | error _ => trivial
  | ok out =>
    rcases out with ⟨⟨result, w'⟩, ambient'⟩
    cases result
    have retained := (ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_retained peer)
      w ambient () w' ambient' hr
    refine ⟨peerPutEvents_safe peer w h hi, retained.unique hi.2.1, ?_⟩
    intro stamp released
    rcases AccessEvent.released_append.mp released with old | new
    · exact retained.absent (hi.2.2 _ old)
    · obtain ⟨pid, p, rfl, hp, hc, rfl⟩ := peerPutEvents_release peer w stamp new
      rw [peerPut_release_snapshot pid w w' ambient ambient' p hp hc hr]
      apply hi.2.1.erase_absent
      change (w.dev.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
      rw [hp]; rfl

theorem wgGetDeviceDonePrefix_preserves (ctx : DumpCtx) :
    StatePrefixPreserves (fun h w _ => AccessInv h w) AccessEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  unfold wgGetDeviceDonePrefix
  apply StatePrefixEnsures.bind (g := liftWGPrefix (branch .getDoneHasWg ctx.hasWg))
  · apply StatePrefixEnsures.lift
    · exact fun _ _ _ hi => hi.1
    · intro h w ambient x w' ambient' hi hr
      simp [branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨_, hw⟩, _⟩
      simpa [← hw] using hi
  · intro _
    exact peerPutPrefix_preserves _

/-- This finite family contains only the complete original release helper and
its dump-completion caller; it does not stand for arbitrary syscalls. -/
inductive AccessCall where
  | put (peer : Option PeerId)
  | dumpDone (ctx : DumpCtx)

namespace AccessCall

def original : AccessCall → WG.M Unit
  | .put peer => peerPut peer
  | .dumpDone ctx => wgGetDeviceDone ctx

def observed : AccessCall → WGPrefix PeerEvent Unit
  | .put peer => peerPutPrefix peer
  | .dumpDone ctx => wgGetDeviceDonePrefix ctx

def execute : List AccessCall → WG.M Unit
  | [] => pure ()
  | call :: calls => call.original >>= fun _ => execute calls

def observe : List AccessCall → WGPrefix PeerEvent Unit
  | [] => pure ()
  | call :: calls => call.observed >>= fun _ => observe calls

theorem erases (call : AccessCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | put peer => exact peerPutPrefix_erases peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_erases ctx

theorem preserves (call : AccessCall) : StatePrefixPreserves (fun h w _ => AccessInv h w) AccessEvent.Safe call.observed := by
  cases call with
  | put peer => exact peerPutPrefix_preserves peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_preserves ctx

theorem observe_erases (calls : List AccessCall) : ErasesStatePrefix (observe calls) (execute calls) := by
  induction calls with
  | nil => exact erasesStatePrefix_pure ()
  | cons call calls ih => exact erasesStatePrefix_bind call.erases (fun _ => ih)

theorem observe_preserves (calls : List AccessCall) :
    StatePrefixPreserves (fun h w _ => AccessInv h w) AccessEvent.Safe (observe calls) := by
  induction calls with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ h => h.1) (fun _ _ _ h => h)
  | cons call calls ih => exact StatePrefixEnsures.bind call.preserves (fun _ => ih)

end AccessCall
end Leanux.Proofs.WG.Peers
