import Leanux.Proofs.WG.Lifetimes.AllocationInvariant

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Complete keypair creation, including allocation refusal and failed hidden
input consumption. The core has no failing action after the insertion, so its
two allocation/write observations may be emitted at its successful return.
All-input equations reproduce even occupied-slot overwrites; AllocationInv
excludes those inputs from the preservation theorem through its slot bound. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def keyAllocationDevice (d : Device) (stamp : Nat) (pid : PeerId) : Device :=
  {d with
    nextKeypairId := d.nextKeypairId + 1
    keypairs := d.keypairs.insert d.nextKeypairId {internalId := stamp, peer := pid}}

def keyAllocationWorld (w : World) (d : Device) (pid : PeerId) : World :=
  {w with k := {w.k with
    keypairCounter := w.k.keypairCounter + 1
    wg := some (keyAllocationDevice d (w.k.keypairCounter + 1) pid)}}

def keypairCreateCore (pid : PeerId) : M KeypairId := do
  let stamp := (← getK).keypairCounter + 1
  modifyK fun k => {k with keypairCounter := stamp}
  let id := (← getDev).nextKeypairId
  modifyDev fun d => {d with nextKeypairId := id + 1}
  setKeypair id {internalId := stamp, peer := pid}
  return id

theorem keypairCreateCore_run (pid : PeerId) (w : World) :
    (keypairCreateCore pid).run w = match w.k.wg with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok (d.nextKeypairId, keyAllocationWorld w d pid) := by
  cases hd : w.k.wg <;>
    simp [keypairCreateCore, getK, modifyK, getDev, modifyDev, setKeypair,
      invariant, hd, keyAllocationWorld, keyAllocationDevice]

def keypairCreateCorePrefix (pid : PeerId) : MixedM KeypairId :=
  fun w => ExceptT.mk fun h => match (keypairCreateCore pid).run w with
    | .error e => (.error e, h)
    | .ok (id, v) => (.ok (id, v), h ++
        [.keypair (.allocate id (w.k.keypairCounter + 1)),
         .keypair (.write id (w.k.keypairCounter + 1))])

@[simp] theorem keypairCreateCorePrefix_run (pid : PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (keypairCreateCorePrefix pid) w h = match (keypairCreateCore pid).run w with
      | .error e => (.error e, h)
      | .ok (id, v) => (.ok (id, v), h ++
          [.keypair (.allocate id (w.k.keypairCounter + 1)),
           .keypair (.write id (w.k.keypairCounter + 1))]) := rfl

theorem keypairCreateCorePrefix_erases (pid : PeerId) :
    ErasesPrefix (keypairCreateCorePrefix pid) (keypairCreateCore pid) := by
  intro w h
  rw [keypairCreateCorePrefix_run]
  cases (keypairCreateCore pid).run w <;> rfl

theorem keyAllocation_store (w : World) (d : Device) (pid : PeerId) (hd : w.k.wg = some d) :
    keyStore (keyAllocationWorld w d pid) = (keyStore w).allocate d.nextKeypairId := by
  apply Store.ext
  · rfl
  · funext j
    simp only [keyStore, keypairResidents, keyAllocationWorld, keyAllocationDevice, hd,
      Option.bind_some, Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq,
      Store.allocate]
    by_cases he : j = d.nextKeypairId <;> simp_all [eq_comm]

theorem AllocationInv.key_allocate (hi : AllocationInv h w) (hd : w.k.wg = some d) (pid : PeerId) :
    AllocationInv (h ++ [.keypair (.allocate d.nextKeypairId (w.k.keypairCounter + 1)),
      .keypair (.write d.nextKeypairId (w.k.keypairCounter + 1))])
      (keyAllocationWorld w d pid) := by
  let v := keyAllocationWorld w d pid
  let events : List LifetimeEvent := [.keypair (.allocate d.nextKeypairId (w.k.keypairCounter + 1)),
      .keypair (.write d.nextKeypairId (w.k.keypairCounter + 1))]
  have hp : Peers.snapshot v = Peers.snapshot w := by
    simp [v, keyAllocationWorld, keyAllocationDevice, Peers.snapshot, hd]
  have ht : packetResidents v = packetResidents w := by
    funext s; cases s <;> simp [v, keyAllocationWorld, keyAllocationDevice, packetResidents, hd]
  have hk := keyAllocation_store w d pid hd
  have hkr : keypairResidents v = insertResident (keypairResidents w) d.nextKeypairId
      (w.k.keypairCounter + 1) := congrArg Store.slots hk
  have fresh : ¬ AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) (w.k.keypairCounter + 1) := by
    intro hr; have := hi.keyPast _ hr; omega
  have hkey := hi.release.1.keypair.allocate (i := d.nextKeypairId) fresh
  have hpeer : Peers.CreationInv ((h ++ events).filterMap LifetimeEvent.peer?) v := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer.congr hp
  have hpacket : ResidentSafe ((h ++ events).filterMap LifetimeEvent.packet?) (packetResidents v) := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?, ht] using hi.release.1.packet
  have hkeys : ResidentSafe ((h ++ events).filterMap LifetimeEvent.keypair?) (keypairResidents v) := by
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, hkr] using hkey
  change AllocationInv (h ++ events) v
  refine ⟨⟨⟨hpeer.access, hkeys, hpacket⟩, ?_⟩, hpeer, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · change Unique (keyStore v)
      rw [hk]
      exact allocate_unique _ _ hi.keyBounded hi.release.2.1
    · change ResidentUnique (packetResidents v)
      rw [ht]; exact hi.release.2.2
  · intro e he i p hl
    simp only [v, keyAllocationWorld, Option.some.injEq] at he
    subst e
    exact hi.peerSlots d hd i p hl
  · rw [hk]; exact allocate_bounded _ _ hi.keyBounded
  · intro s hs
    have old : AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) s := by
      simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.keypair?, AccessEvent.Released] using hs
    exact Nat.le_trans (hi.keyPast s old) (Nat.le_succ _)
  · intro e he i k hl
    simp only [v, keyAllocationWorld, Option.some.injEq] at he
    subst e
    simp only [keyAllocationDevice, Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq] at hl ⊢
    split at hl
    · rename_i he
      subst i
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (hi.keySlots d hd i k hl) (Nat.lt_succ_self _)
  · intro e he
    simp only [v, keyAllocationWorld, Option.some.injEq] at he
    subst e
    exact hi.packetBounded d hd
  · intro e he
    simp only [v, keyAllocationWorld, Option.some.injEq] at he
    subst e
    exact hi.epochBounded d hd
  · intro s hs
    apply hi.packetPastEpoch s
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hs
  · intro e he s hs
    simp only [v, keyAllocationWorld, Option.some.injEq] at he
    subst e
    apply hi.packetPast d hd s
    simpa [events, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?, keyAllocationDevice] using hs

theorem keypairCreateCorePrefix_preserves (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keypairCreateCorePrefix pid) := by
  intro w h hi
  rw [keypairCreateCorePrefix_run, keypairCreateCore_run]
  cases hd : w.k.wg with
  | none => exact ⟨[], by simp, hi.safe, True.intro⟩
  | some d =>
    have hn := hi.key_allocate hd pid
    exact ⟨_, rfl, hn.safe, hn⟩

def keypairCreatePrefix (pid : PeerId) : MixedM (Option KeypairId) := do
  let ok ← liftPrefix (hiddenAlloc .kzallocKeypair)
  if ← liftPrefix (branch .keypairCreateNoMem !ok) then return none
  return some (← keypairCreateCorePrefix pid)

theorem keypairCreate_factor (pid : PeerId) : keypairCreate pid = (do
    let ok ← hiddenAlloc .kzallocKeypair
    if ← branch .keypairCreateNoMem !ok then return none
    return some (← keypairCreateCore pid)) := by
  simp [keypairCreate, keypairCreateCore]

theorem keypairCreatePrefix_erases (pid : PeerId) :
    ErasesPrefix (keypairCreatePrefix pid) (keypairCreate pid) := by
  rw [keypairCreate_factor]
  unfold keypairCreatePrefix
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro ok
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro no
  split
  · exact erasesPrefix_pure _
  · exact erasesPrefix_bind (keypairCreateCorePrefix_erases pid) (fun id => erasesPrefix_pure (some id))

theorem keypairCreatePrefix_preserves (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keypairCreatePrefix pid) := by
  unfold keypairCreatePrefix
  apply PrefixPreserves.bind (allocation_kernel _ (hiddenAlloc_sameKernel _))
  intro ok
  apply PrefixPreserves.bind (allocation_kernel _ (sameKernel_branch _ _))
  intro no
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
  · exact PrefixPreserves.bind (keypairCreateCorePrefix_preserves pid)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _)

/-- Exact observations on every original outcome. Hidden-input failure and
normal allocation refusal have no resolved object access; a successful
insertion records its new identity and initializing write. -/
theorem keypairCreatePrefix_observation (pid : PeerId) (w : World) (h : List LifetimeEvent) :
    runPrefix (keypairCreatePrefix pid) w h = match (keypairCreate pid).run w with
      | .error e => (.error e, h)
      | .ok (none, v) => (.ok (none, v), h)
      | .ok (some id, v) => (.ok (some id, v), h ++
          [.keypair (.allocate id (w.k.keypairCounter + 1)),
           .keypair (.write id (w.k.keypairCounter + 1))]) := by
  rw [keypairCreate_factor]
  simp only [keypairCreatePrefix, runPrefix_bind, runPrefix_lift, StateT.run_bind]
  cases ha : (hiddenAlloc .kzallocKeypair).run w with
  | error e => simp
  | ok out =>
    rcases out with ⟨ok, v⟩
    have hk := hiddenAlloc_sameKernel .kzallocKeypair w ok v ha
    cases ok <;>
      simp [branch, keypairCreateCore_run,
        keyAllocationWorld, hk]
    rw [map_eq_pure_bind, runPrefix_bind, keypairCreateCorePrefix_run, keypairCreateCore_run]
    cases w.k.wg <;> simp [keyAllocationWorld]

/-- A failed creation retains the incoming history exactly. -/
theorem keypairCreatePrefix_failure (pid : PeerId) (w : World) (h : List LifetimeEvent) (e : Stop)
    (hr : (keypairCreate pid).run w = .error e) :
    runPrefix (keypairCreatePrefix pid) w h = (.error e, h) := by
  rw [keypairCreatePrefix_observation, hr]

/-- Ordinary memory-allocation refusal also leaves the history unchanged. -/
theorem keypairCreatePrefix_refusal (pid : PeerId) (w v : World) (h : List LifetimeEvent)
    (hr : (keypairCreate pid).run w = .ok (none, v)) :
    runPrefix (keypairCreatePrefix pid) w h = (.ok (none, v), h) := by
  rw [keypairCreatePrefix_observation, hr]

end Leanux.Proofs.WG.Lifetimes
