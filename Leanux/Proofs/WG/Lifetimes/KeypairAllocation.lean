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

def keyAllocationDevice (d : Device) (stamp : Nat) (pid : Option PeerId) : Device :=
  {d with
    nextKeypairId := d.nextKeypairId + 1
    keypairs := d.keypairs.insert d.nextKeypairId {internalId := stamp, peer := pid}}

def keyAllocationWorld (w : WGWorld) (d : Device) (pid : Option PeerId) : WGWorld :=
  {w with
    keypairCounter := w.keypairCounter + 1
    dev := some (keyAllocationDevice d (w.keypairCounter + 1) pid)}

def keypairCreateCore (pid : Option PeerId) : WG.M KeypairId := do
  let stamp := (← get).keypairCounter + 1
  modify fun k => {k with keypairCounter := stamp}
  let id := (← getDev).nextKeypairId
  modifyDev fun d => {d with nextKeypairId := id + 1}
  setKeypair id {internalId := stamp, peer := pid}
  return id

theorem keypairCreateCore_run (pid : Option PeerId) (w : WGWorld) (ambient : Ambient) :
    ((keypairCreateCore pid).run w).run ambient = match w.dev with
      | none => .error (.invariant "no WireGuard device in this trace's fixture")
      | some d => .ok ((d.nextKeypairId, keyAllocationWorld w d pid), ambient) := by
  cases hd : w.dev <;>
    simp [keypairCreateCore, getDev, modifyDev, setKeypair,
      invariant, AmbientM.invariant, hd, keyAllocationWorld, keyAllocationDevice]
  all_goals rfl

def keypairCreateCorePrefix (pid : Option PeerId) : MixedM KeypairId :=
  fun w ambient => ExceptT.mk fun h => match ((keypairCreateCore pid).run w).run ambient with
    | .error e => (.error e, h)
    | .ok ((id, v), ambient') => (.ok ((id, v), ambient'), h ++
        [.keypair (.allocate id (w.keypairCounter + 1)),
         .keypair (.write id (w.keypairCounter + 1))])

@[simp] theorem keypairCreateCorePrefix_run (pid : Option PeerId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairCreateCorePrefix pid) w ambient h = match ((keypairCreateCore pid).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((id, v), ambient') => (.ok ((id, v), ambient'), h ++
          [.keypair (.allocate id (w.keypairCounter + 1)),
           .keypair (.write id (w.keypairCounter + 1))]) := rfl

theorem keypairCreateCorePrefix_erases (pid : Option PeerId) :
    ErasesStatePrefix (keypairCreateCorePrefix pid) (keypairCreateCore pid) := by
  intro w ambient h
  change (runStatePrefix (keypairCreateCorePrefix pid) w ambient h).1 = _
  rw [keypairCreateCorePrefix_run]
  cases ((keypairCreateCore pid).run w).run ambient <;> rfl

theorem keyAllocation_store (w : WGWorld) (d : Device) (pid : Option PeerId) (hd : w.dev = some d) :
    keyStore (keyAllocationWorld w d pid) = (keyStore w).allocate d.nextKeypairId := by
  apply Store.ext
  · rfl
  · funext j
    simp only [keyStore, keypairResidents, keyAllocationWorld, keyAllocationDevice, hd,
      Option.bind_some, Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq,
      Store.allocate]
    by_cases he : j = d.nextKeypairId <;> simp_all [eq_comm]

theorem AllocationInv.key_allocate (hi : AllocationInv h w) (hd : w.dev = some d) (pid : Option PeerId) :
    AllocationInv (h ++ [.keypair (.allocate d.nextKeypairId (w.keypairCounter + 1)),
      .keypair (.write d.nextKeypairId (w.keypairCounter + 1))])
      (keyAllocationWorld w d pid) := by
  let v := keyAllocationWorld w d pid
  let events : List LifetimeEvent := [.keypair (.allocate d.nextKeypairId (w.keypairCounter + 1)),
      .keypair (.write d.nextKeypairId (w.keypairCounter + 1))]
  have hp : Peers.snapshot v = Peers.snapshot w := by
    simp [v, keyAllocationWorld, keyAllocationDevice, Peers.snapshot, hd]
  have ht : packetResidents v = packetResidents w := by
    funext s; cases s <;> simp [v, keyAllocationWorld, keyAllocationDevice, packetResidents, hd]
  have hk := keyAllocation_store w d pid hd
  have hkr : keypairResidents v = insertResident (keypairResidents w) d.nextKeypairId
      (w.keypairCounter + 1) := congrArg Store.slots hk
  have fresh : ¬ AccessEvent.Released (h.filterMap LifetimeEvent.keypair?) (w.keypairCounter + 1) := by
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

theorem keypairCreateCorePrefix_preserves (pid : Option PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keypairCreateCorePrefix pid) := by
  intro w ambient h hi
  have observed := keypairCreateCorePrefix_run pid w ambient h
  simp only [runStatePrefix] at observed
  rw [observed, keypairCreateCore_run]
  cases hd : w.dev with
  | none => exact ⟨[], by simp, hi.safe, True.intro⟩
  | some d =>
    have hn := hi.key_allocate hd pid
    exact ⟨_, rfl, hn.safe, hn⟩

def keypairCreatePrefix (pid : Option PeerId) : MixedM (Option KeypairId) := do
  let ok ← liftWGPrefix (hiddenAlloc .kzallocKeypair)
  if ← liftWGPrefix (branch .keypairCreateNoMem !ok) then return none
  return some (← keypairCreateCorePrefix pid)

theorem keypairCreate_factor (pid : Option PeerId) : keypairCreate pid = (do
    let ok ← hiddenAlloc .kzallocKeypair
    if ← branch .keypairCreateNoMem !ok then return none
    return some (← keypairCreateCore pid)) := by
  simp [keypairCreate, keypairCreateCore]

theorem keypairCreatePrefix_erases (pid : Option PeerId) :
    ErasesStatePrefix (keypairCreatePrefix pid) (keypairCreate pid) := by
  rw [keypairCreate_factor]
  unfold keypairCreatePrefix
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro ok
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro no
  split
  · exact erasesStatePrefix_pure _
  · exact erasesStatePrefix_bind (keypairCreateCorePrefix_erases pid) (fun id => erasesStatePrefix_pure (some id))

theorem keypairCreatePrefix_preserves (pid : Option PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keypairCreatePrefix pid) := by
  unfold keypairCreatePrefix
  apply StatePrefixEnsures.bind (allocation_state_store _ (by
    intro initial
    exact hoare_liftAmbient (AmbientM.hiddenAlloc _) (fun w => wgStoreView w = initial)))
  intro ok
  apply StatePrefixEnsures.bind (allocation_state_store _ (by
    intro initial
    exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)))
  intro no
  split
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
  · exact StatePrefixEnsures.bind (keypairCreateCorePrefix_preserves pid)
      (fun _ => StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi))

/-- Exact observations on every original outcome. Hidden-input failure and
normal allocation refusal have no resolved object access; a successful
insertion records its new identity and initializing write. -/
theorem keypairCreatePrefix_observation (pid : Option PeerId) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairCreatePrefix pid) w ambient h =
      match ((keypairCreate pid).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((none, v), ambient') => (.ok ((none, v), ambient'), h)
      | .ok ((some id, v), ambient') => (.ok ((some id, v), ambient'), h ++
          [.keypair (.allocate id (w.keypairCounter + 1)),
           .keypair (.write id (w.keypairCounter + 1))]) := by
  rw [keypairCreate_factor]
  simp only [keypairCreatePrefix, runStatePrefix_bind, liftWGPrefix,
    runStatePrefix_lift, StateT.run_bind]
  cases ha : ((hiddenAlloc .kzallocKeypair : WG.M Bool).run w).run ambient with
  | error e => simp
  | ok out =>
    rcases out with ⟨⟨ok, v⟩, ambient'⟩
    have hv : v = w := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) (fun v => v = w))
      w ambient ok v ambient' rfl ha
    subst v
    cases ok <;>
      simp [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
        keypairCreateCore_run, keyAllocationWorld]
    rw [map_eq_pure_bind, runStatePrefix_bind, keypairCreateCorePrefix_run, keypairCreateCore_run]
    cases w.dev <;> simp [keyAllocationWorld]

/-- A failed creation retains the incoming history exactly. -/
theorem keypairCreatePrefix_failure (pid : Option PeerId) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) (e : Stop)
    (hr : ((keypairCreate pid).run w).run ambient = .error e) :
    runStatePrefix (keypairCreatePrefix pid) w ambient h = (.error e, h) := by
  rw [keypairCreatePrefix_observation, hr]

/-- Ordinary memory-allocation refusal also leaves the history unchanged. -/
theorem keypairCreatePrefix_refusal (pid : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient) (h : List LifetimeEvent)
    (hr : ((keypairCreate pid).run w).run ambient = .ok ((none, v), ambient')) :
    runStatePrefix (keypairCreatePrefix pid) w ambient h = (.ok ((none, v), ambient'), h) := by
  rw [keypairCreatePrefix_observation, hr]

end Leanux.Proofs.WG.Lifetimes
