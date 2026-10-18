import Leanux.Proofs.WG.HandshakeSecurity.FreshnessAllocation
import Leanux.Proofs.WG.HandshakeSecurity.Increasing

/-! Timestamp history indexed by allocation identity. A fresh peer need not
inherit the old occupant's timestamp when a numeric slot is reused. The
ledger's allocation bound makes this separation explicit at native creation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

abbrev Ledger := Nat → Option (List UInt8)

def Coherent (ledger : Ledger) (w : WGWorld) : Prop :=
  ∀ pid stamp, freshnessAt w pid = some stamp →
    ledger stamp.1 = none ∨ ledger stamp.1 = some stamp.2

def Bounded (ledger : Ledger) (frontier : Nat) : Prop :=
  ∀ identity timestamp, ledger identity = some timestamp → identity ≤ frontier

def Inv (ledger : Ledger) (w : WGWorld) : Prop :=
  Bounded ledger w.peerCounter ∧ Coherent ledger w

def put (ledger : Ledger) (identity : Nat) (timestamp : List UInt8) : Ledger :=
  fun current => if current = identity then some timestamp else ledger current

theorem initial (w : WGWorld) : Inv (fun _ => none) w :=
  ⟨fun _ _ impossible => (by cases impossible), fun _ _ _ => Or.inl rfl⟩

theorem retained {ledger : Ledger} {w v : WGWorld} (hi : Inv ledger w)
    (frame : RetainsFreshness w v) (counter : w.peerCounter ≤ v.peerCounter) : Inv ledger v :=
  ⟨fun identity timestamp found => Nat.le_trans (hi.1 identity timestamp found) counter,
   fun pid stamp found => hi.2 pid stamp (frame pid stamp found)⟩

theorem fresh_absent {ledger : Ledger} {frontier identity : Nat}
    (hi : Bounded ledger frontier) (fresh : frontier < identity) : ledger identity = none := by
  cases found : ledger identity with
  | none => rfl
  | some timestamp => exact False.elim (Nat.not_le_of_gt fresh (hi identity timestamp found))

theorem allocate {ledger : Ledger} {w : WGWorld} (hi : Inv ledger w)
    (pid : PeerId) (key : Key) : Inv ledger (Peers.creationCoreWorld w pid key) := by
  constructor
  · intro identity timestamp found
    exact Nat.le_trans (hi.1 identity timestamp found) (Nat.le_succ _)
  · intro q stamp found
    rcases Freshness.creation_core pid key w q stamp found with old | birth
    · exact hi.2 q stamp old
    · subst stamp
      exact Or.inl (fresh_absent hi.1 (Nat.lt_succ_self _))

theorem allocation_core (ledger : Ledger) (pid : PeerId) (key : Key) :
    Framing.Preserves (Inv ledger) (Peers.peerCreateCore pid key) := by
  apply (Framing.hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [Peers.peerCreateCore_run] at run
  cases run
  exact allocate hi pid key

theorem identity_resident {w : WGWorld} {pid : PeerId} {stamp : Nat × List UInt8}
    (found : freshnessAt w pid = some stamp) : (Peers.snapshot w).slots pid = some stamp.1 := by
  have mapped := congrArg (Option.map Prod.fst) found
  simpa only [freshnessAt,Peers.snapshot,Option.map_map,Function.comp_def,Option.map_some] using mapped

theorem write {ledger : Ledger} {r : TimestampReceipt}
    (hi : Inv ledger r.execution.before) (valid : r.Valid)
    (bounded : Lifetimes.Bounded (Peers.snapshot r.execution.before))
    (unique : Unique (Peers.snapshot r.execution.before)) :
    ∃ identity old,
      freshnessAt r.execution.before r.peer = some (identity,old) ∧
      (ledger identity = none ∨ ledger identity = some old) ∧
      Inv (put ledger identity r.received) r.execution.after := by
  obtain ⟨d,p,hd,hp,after,_⟩ := write_effect r.peer r.received r.execution valid
  have before : freshnessAt r.execution.before r.peer = some (p.internalId,p.latestTimestamp) := by
    simp [freshnessAt,hd,hp]
  refine ⟨p.internalId,p.latestTimestamp,before,hi.2 r.peer _ before,?_,?_⟩
  · intro identity timestamp found
    rw [after]
    change identity ≤ r.execution.before.peerCounter
    by_cases eq : identity = p.internalId
    · subst identity
      exact bounded r.peer p.internalId (identity_resident before)
    · exact hi.1 identity timestamp (by simpa [put,eq] using found)
  · intro q stamp found
    by_cases same : q = r.peer
    · subst q
      have eq : stamp = (p.internalId,r.received) := by
        simpa [freshnessAt,after] using found.symm
      subst stamp
      exact Or.inr (by simp [put])
    · have old : freshnessAt r.execution.before q = some stamp := by
        simpa [freshnessAt,after,hd,Std.TreeMap.getElem?_insert,Ne.symm same] using found
      have different : stamp.1 ≠ p.internalId := by
        intro eq
        apply same
        exact unique q r.peer p.internalId
          (by simpa only [eq] using identity_resident old) (identity_resident before)
      simpa only [put,different,↓reduceIte] using hi.2 q stamp old

def applyReceipt (ledger : Ledger) (r : TimestampReceipt) : Ledger :=
  match freshnessAt r.execution.before r.peer with
  | none => ledger
  | some stamp => put ledger stamp.1 r.received

def replay (history : List TimestampReceipt) : Ledger :=
  history.foldl applyReceipt (fun _ => none)

theorem replay_append (history : List TimestampReceipt) (r : TimestampReceipt) :
    replay (history ++ [r]) = applyReceipt (replay history) r := by
  simp [replay,List.foldl_append]

def Linked (ledger : Ledger) (r : TimestampReceipt) : Prop :=
  ∃ identity old, freshnessAt r.execution.before r.peer = some (identity,old) ∧
    (ledger identity = none ∨ ledger identity = some old) ∧
    memcmp r.received old = .gt

inductive History : List TimestampReceipt → Prop where
  | empty : History []
  | next {history : List TimestampReceipt} (r : TimestampReceipt)
      (prior : History history) (valid : r.Valid)
      (linked : Linked (replay history) r) : History (history ++ [r])

def StateInv (history : List TimestampReceipt) (w : WGWorld) : Prop :=
  History history ∧ Inv (replay history) w ∧
  Lifetimes.Bounded (Peers.snapshot w) ∧ Unique (Peers.snapshot w)

theorem write_snapshot (r : TimestampReceipt) (valid : r.Valid) :
    Peers.snapshot r.execution.after = Peers.snapshot r.execution.before := by
  obtain ⟨d,p,hd,hp,after,_⟩ := write_effect r.peer r.received r.execution valid
  rw [after]
  apply Store.ext
  · rfl
  · funext q
    by_cases eq : r.peer = q
    · subst q
      simp [Peers.snapshot,hd,hp]
    · simp [Peers.snapshot,hd,Std.TreeMap.getElem?_insert,eq]

theorem append (history : List TimestampReceipt) (r : TimestampReceipt)
    (hi : StateInv history r.execution.before) (valid : r.Valid) (newer : r.Increasing) :
    StateInv (history ++ [r]) r.execution.after := by
  obtain ⟨identity,old,resident,linked,carried⟩ := write hi.2.1 valid hi.2.2.1 hi.2.2.2
  have increasing : memcmp r.received old = .gt := by
    obtain ⟨prior,found,comparison⟩ := newer
    have actual : latestAt r.execution.before r.peer = some old := by
      have mapped := congrArg (Option.map Prod.snd) resident
      simpa only [freshnessAt,latestAt,Option.map_map,Function.comp_def,Option.map_some] using mapped
    have eq : prior = old := Option.some.inj (found.symm.trans actual)
    simpa only [eq] using comparison
  refine ⟨.next r hi.1 valid ⟨identity,old,resident,linked,increasing⟩,?_,?_,?_⟩
  · simpa only [replay_append,applyReceipt,resident] using carried
  · simpa only [write_snapshot r valid] using hi.2.2.1
  · simpa only [write_snapshot r valid] using hi.2.2.2

theorem identity_timestamp {w : WGWorld} {pid identity : Nat}
    (found : (Peers.snapshot w).slots pid = some identity) :
    ∃ timestamp, freshnessAt w pid = some (identity,timestamp) := by
  obtain ⟨p,resident,equal⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨d,hd,hp⟩ := Option.bind_eq_some_iff.mp resident
  exact ⟨p.latestTimestamp,by simp [freshnessAt,hd,hp,equal]⟩

theorem state_retained {history : List TimestampReceipt} {w v : WGWorld}
    (hi : StateInv history w) (frame : RetainsFreshness w v)
    (counter : w.peerCounter ≤ v.peerCounter) : StateInv history v := by
  have identities : ∀ pid identity, (Peers.snapshot v).slots pid = some identity →
      (Peers.snapshot w).slots pid = some identity := by
    intro pid identity found
    obtain ⟨timestamp,resident⟩ := identity_timestamp found
    exact identity_resident (frame pid (identity,timestamp) resident)
  refine ⟨hi.1,retained hi.2.1 frame counter,?_,?_⟩
  · intro pid identity found
    exact Nat.le_trans (hi.2.2.1 pid identity (identities pid identity found)) counter
  · intro pid q identity found other
    exact hi.2.2.2 pid q identity (identities pid identity found) (identities q identity other)

theorem state_allocate {history : List TimestampReceipt} {w : WGWorld}
    (hi : StateInv history w) (pid : PeerId) (key : Key) :
    StateInv history (Peers.creationCoreWorld w pid key) := by
  refine ⟨hi.1,allocate hi.2.1 pid key,?_,?_⟩
  · cases hd : w.dev with
    | none => intro q identity found; simp [Peers.snapshot,Peers.creationCoreWorld,hd] at found
    | some d =>
      rw [Peers.creationCore_snapshot pid key w d hd]
      exact allocate_bounded _ _ hi.2.2.1
  · cases hd : w.dev with
    | none => intro q j identity found _; simp [Peers.snapshot,Peers.creationCoreWorld,hd] at found
    | some d =>
      rw [Peers.creationCore_snapshot pid key w d hd]
      exact allocate_unique _ _ hi.2.2.1 hi.2.2.2

theorem state_initial (net bare : Bool) : StateInv [] (Runner.initialWG net bare) := by
  refine ⟨.empty,initial _,?_,?_⟩
  · intro pid identity found
    cases net <;> cases bare <;> simp [Peers.snapshot,Runner.initialWG] at found
  · intro pid q identity found _
    cases net <;> cases bare <;> simp [Peers.snapshot,Runner.initialWG] at found

theorem timestamp (pid : PeerId) (old t : List UInt8) :
    StatePrefixEnsures
      (fun h w _ => StateInv h w ∧ latestAt w pid = some old)
      History (timestampObserved pid old t)
      (fun _ h w _ => StateInv h w) := by
  intro w a h hi
  have equation := timestamp_run pid old t w a h
  unfold runWGPrefix runStatePrefix at equation
  rw [equation]
  split
  next newer =>
    cases run : ((writeTimestamp pid t).run w).run
        (CounterWindow.record a .consumeNewerTimestamp true) with
    | error stop => exact ⟨[],by simp,hi.1.1,trivial⟩
    | ok out =>
      rcases out with ⟨⟨x,v⟩,b⟩
      have next := append h
        ⟨pid,old,t,⟨x,w,v,CounterWindow.record a .consumeNewerTimestamp true,b⟩⟩
        hi.1 run ⟨old,hi.2,by simpa only [beq_iff_eq] using newer⟩
      exact ⟨_,rfl,next.1,next⟩
  next => exact ⟨[],by simp,hi.1.1,hi.1⟩

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
