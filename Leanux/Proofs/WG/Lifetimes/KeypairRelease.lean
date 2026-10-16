import Leanux.Proofs.WG.Lifetimes.ReleaseInvariant
import Leanux.Proofs.WG.Lifetimes.IndexOwnerAccess

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The original keypair reference helpers with resolved-object observations.
Each removal first resolves the embedded peer word through the keypair owner.
Only the subsequent index-table filter is access-free. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def removeKeypairIndex (id : KeypairId) : WG.M Unit := liftIndex (indexRemove (.keypair id))

theorem removeKeypairIndex_identity (id : KeypairId) : SameView identityView (removeKeypairIndex id) := by
  apply SameView.of_wp
  intro initial
  apply hoare_liftIndex (indexRemove (.keypair id))
  intro w d table hi hd
  have he : identityView {w with dev := some {d with indexTable := table}} = identityView w := by
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp only [hd, Option.bind_some, Option.map_some]
  exact he.trans hi

/-- Both original unhash sites first resolve the owner's peer word. -/
def removeKeypairEntryPrefix (id : KeypairId) : MixedM Unit := do
  _ ← peerDerefPrefix (.keypair id)
  liftWGPrefix (removeKeypairIndex id)

theorem removeKeypairEntryPrefix_erases (id : KeypairId) :
    ErasesStatePrefix (removeKeypairEntryPrefix id)
      (do _ ← IndexOwner.peerDeref (.keypair id); indexRemove (.keypair id)) :=
  erasesStatePrefix_bind (peerDerefPrefix_erases _) (fun _ => erasesStatePrefix_lift _)

theorem removeKeypairEntryPrefix_spec (P : IdentityView → Prop) (id : KeypairId) :
    MixedSpec P (removeKeypairEntryPrefix id) (fun _ => P) := by
  apply StatePrefixEnsures.bind (peerDerefPrefix_spec mixedAmbient P (.keypair id))
  intro _
  exact mixed_state_lift P _ (removeKeypairIndex_identity id)

/-- This leaf emits a supplied stamp. Its resolved-release interpretation
requires the current-resident premise in eraseKeypairPrefix_spec. -/
def eraseKeypairPrefix (id stamp : Nat) : MixedM Unit :=
  fun w ambient => ExceptT.mk fun h =>
    (((modifyDev fun d => {d with keypairs := d.keypairs.erase id}).run w).run ambient,
      h ++ [.keypair (.release id stamp)])

theorem eraseKeypairPrefix_erases (id stamp : Nat) :
    ErasesStatePrefix (eraseKeypairPrefix id stamp)
      (modifyDev fun d => {d with keypairs := d.keypairs.erase id}) := fun _ _ _ => rfl

theorem eraseKeypairPrefix_spec (id stamp : Nat) :
    MixedSpec (fun s => ReleaseUnique s ∧ s.2.1 id = some stamp)
      (eraseKeypairPrefix id stamp) (fun _ => ReleaseUnique) := by
  intro w ambient h hi
  let v := Packets.update w fun d => {d with keypairs := d.keypairs.erase id}
  have hp : Peers.snapshot v = Peers.snapshot w := by
    simp [v, Packets.update, Peers.snapshot, Option.bind_map, Function.comp_def]
  have hk : keypairResidents v = eraseResident (keypairResidents w) id := by
    funext j
    cases hd : w.dev with
    | none => simp [v, Packets.update, keypairResidents, eraseResident, hd]
    | some d =>
      by_cases he : j = id
      · subst j
        simp [v, Packets.update, keypairResidents, eraseResident, hd]
      · simp [v, Packets.update, keypairResidents, eraseResident, hd,
          Std.TreeMap.getElem?_erase, he, Ne.symm he]
  have ht : packetResidents v = packetResidents w := by
    funext slot
    cases slot <;> cases hd : w.dev <;> simp [v, Packets.update, packetResidents, hd]
  have hn := ReleaseInv.keyRelease (show ReleaseInv h w from ⟨hi.1, hi.2.1⟩) hi.2.2 hp hk ht
  exact ⟨[.keypair (.release id stamp)], rfl, hn.safe, hn⟩

def keypairGetPrefix (kp : Option KeypairId) : MixedM (Option KeypairId) := do
  if ← liftWGPrefix (branch .keypairGetNull kp.isNone) then return none
  let some id := kp | liftWGPrefix (invariant "unreachable")
  let k ← getKeypairPrefix id
  if ← liftWGPrefix (branch .keypairGetZero !(← liftWGPrefix (refcountIncNotZero k.refcount))) then return none
  setKeypairPrefix id {k with refcount := k.refcount + 1}
  return some id

def keypairPutPrefix (kp : Option KeypairId) (unreferenceNow : Bool) : MixedM Unit := do
  if ← liftWGPrefix (branch .keypairPutNull kp.isNone) then return
  let some id := kp | liftWGPrefix (invariant "unreachable")
  let k ← getKeypairPrefix id
  if ← liftWGPrefix (branch .keypairPutUnreferenceNow unreferenceNow) then
    removeKeypairEntryPrefix id
  setKeypairPrefix id {k with refcount := k.refcount - 1}
  if ← liftWGPrefix (branch .keypairKrefPutReleased (← liftWGPrefix (refcountDecAndTest k.refcount))) then
    removeKeypairEntryPrefix id
    eraseKeypairPrefix id k.internalId

theorem keypairGetPrefix_erases (kp : Option KeypairId) :
    ErasesStatePrefix (keypairGetPrefix kp) (keypairGet kp) := by
  unfold keypairGetPrefix keypairGet
  repeat' first
    | rfl
    | exact getKeypairPrefix_erases _
    | exact setKeypairPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | intro x
    | split
  all_goals simp_all

theorem keypairPutPrefix_erases (kp : Option KeypairId) (now : Bool) :
    ErasesStatePrefix (keypairPutPrefix kp now) (keypairPut kp now) := by
  unfold keypairPutPrefix keypairPut
  repeat' first
    | rfl
    | exact getKeypairPrefix_erases _
    | exact setKeypairPrefix_erases _ _
    | exact eraseKeypairPrefix_erases _ _
    | exact removeKeypairEntryPrefix_erases _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | intro x
    | split
  all_goals simp_all

theorem keypairGetPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (kp : Option KeypairId) :
    AmbientSpec I P (keypairGetPrefix kp) (fun _ => P) := by
  unfold keypairGetPrefix
  apply StatePrefixEnsures.bind (c.branch P _ _)
  intro isNull
  split
  · exact c.pure P _
  · cases kp with
    | some id =>
      apply StatePrefixEnsures.bind (c.getKeypair P id)
      intro k
      let Q := fun s : IdentityView => P s ∧ s.2.1 id = some k.internalId
      apply StatePrefixEnsures.bind (c.store Q _ (by
        have factor : (refcountIncNotZero k.refcount : WG.M Bool) =
            StateT.lift (refcountIncNotZero k.refcount : AmbientM Bool) := by
          change (refcountIncNotZero k.refcount : WG.M Bool) =
            (monadLift (refcountIncNotZero k.refcount : AmbientM Bool) : WG.M Bool)
          simp only [refcountIncNotZero, branch, branchCmp, unsupported, monadLift_self,
            monadLift_bind, monadLift_pure, apply_ite]
        rw [factor]
        intro initial
        exact hoare_liftAmbient (refcountIncNotZero k.refcount : AmbientM Bool)
          (fun w => wgStoreView w = initial)))
      intro nz
      apply StatePrefixEnsures.bind (c.branch Q _ _)
      intro zero
      split
      · exact (c.pure Q none).consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
      · apply StatePrefixEnsures.bind (c.setKeypair P id {k with refcount := k.refcount + 1})
        intro _
        exact c.pure P _
    | none => exact c.invariant P _

theorem keypairGetPrefix_spec (P : IdentityView → Prop) (kp : Option KeypairId) :
    MixedSpec P (keypairGetPrefix kp) (fun _ => P) :=
  keypairGetPrefix_spec_ambient mixedAmbient P kp

theorem keypairPutPrefix_preserves (kp : Option KeypairId) (now : Bool) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (keypairPutPrefix kp now) := by
  change MixedSpec ReleaseUnique (keypairPutPrefix kp now) (fun _ => ReleaseUnique)
  unfold keypairPutPrefix
  apply StatePrefixEnsures.bind (mixed_branch ReleaseUnique _ _)
  intro isNull
  split
  · exact mixedAmbient.pure ReleaseUnique _
  · cases kp with
    | some id =>
      apply StatePrefixEnsures.bind (mixed_getKeypair ReleaseUnique id)
      intro k
      let P := fun s : IdentityView => ReleaseUnique s ∧ s.2.1 id = some k.internalId
      have tail : MixedSpec P
          (do setKeypairPrefix id {k with refcount := k.refcount - 1}
              if ← liftWGPrefix (branch .keypairKrefPutReleased (← liftWGPrefix (refcountDecAndTest k.refcount))) then
                removeKeypairEntryPrefix id
                eraseKeypairPrefix id k.internalId)
          (fun _ => ReleaseUnique) := by
        apply StatePrefixEnsures.bind ((mixed_setKeypair P id {k with refcount := k.refcount - 1}).consequence
          (fun _ _ _ hi => ⟨hi.1, hi.2, hi.2.2⟩) (fun _ _ _ _ hi => hi))
        intro _
        apply StatePrefixEnsures.bind (mixedAmbient.store P _ (by
          have factor : (refcountDecAndTest k.refcount : WG.M Bool) =
              StateT.lift (refcountDecAndTest k.refcount : AmbientM Bool) := by
            change (refcountDecAndTest k.refcount : WG.M Bool) =
              (monadLift (refcountDecAndTest k.refcount : AmbientM Bool) : WG.M Bool)
            simp only [refcountDecAndTest, branch, branchCmp, unsupported, monadLift_self,
              monadLift_bind, monadLift_pure, apply_ite]
          rw [factor]
          intro initial
          exact hoare_liftAmbient (refcountDecAndTest k.refcount : AmbientM Bool)
            (fun w => wgStoreView w = initial)))
        intro released
        apply StatePrefixEnsures.bind (mixed_branch P _ _)
        intro yes
        split
        · apply StatePrefixEnsures.bind (removeKeypairEntryPrefix_spec P id)
          intro _
          exact eraseKeypairPrefix_spec id k.internalId
        · exact (mixedAmbient.pure P ()).consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => ⟨hi.1, hi.2.1⟩)
      apply StatePrefixEnsures.bind (mixed_branch P _ _)
      intro unreference
      split
      · apply StatePrefixEnsures.bind (removeKeypairEntryPrefix_spec P id)
        intro _
        exact tail
      · exact tail
    | none => exact mixed_invariant ReleaseUnique _

theorem keypairGetPrefix_preserves (kp : Option KeypairId) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (keypairGetPrefix kp) :=
  keypairGetPrefix_spec ReleaseUnique kp

/-- Event counts depend on the entry actually resolved, including failing
reference-count helpers. No event is recorded for an unsuccessful getter. -/
def keypairGetEvents (kp : Option KeypairId) (w : WGWorld) : List LifetimeEvent :=
  match kp.bind (fun i => (w.dev.bind fun d => d.keypairs[i]?).map (fun k => (i, k))) with
  | none => []
  | some (i, k) => [.keypair (.read i k.internalId)] ++
      if k.refcount = 0 ∨ k.refcount + 1 ≥ 2 ^ 31 then [] else [.keypair (.write i k.internalId)]

/-- Exact resolved accesses, including the NULL failure before a decrement
or before the final erase. A count of one alone does not imply a release. -/
def keypairPutEvents (kp : Option KeypairId) (now : Bool) (w : WGWorld) : List LifetimeEvent :=
  match kp.bind (fun i => (w.dev.bind fun d => d.keypairs[i]?).map (fun k => (i, k))) with
  | none => []
  | some (i, k) =>
      let read := LifetimeEvent.keypair (.read i k.internalId)
      [read] ++ (if now then [read] else []) ++
        if now && k.peer.isNone then [] else
          [.keypair (.write i k.internalId)] ++
            if k.refcount = 1 then
              [read] ++ (if k.peer.isSome then [.keypair (.release i k.internalId)] else [])
            else []

@[simp] theorem eraseKeypairPrefix_run (id stamp : Nat) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (eraseKeypairPrefix id stamp) w ambient h =
      (((modifyDev fun d => {d with keypairs := d.keypairs.erase id}).run w).run ambient,
        h ++ [.keypair (.release id stamp)]) := rfl

theorem keypairGetPrefix_events (kp : Option KeypairId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    (runStatePrefix (keypairGetPrefix kp) w ambient h).2 = h ++ keypairGetEvents kp w := by
  cases kp with
  | none => simp [keypairGetPrefix, keypairGetEvents, runStatePrefix_bind, liftWGPrefix, branch, AmbientM.branch,
      StateT.run_bind, StateT.run_pure] <;> rfl
  | some i =>
    cases hd : w.dev with
    | none => simp [keypairGetPrefix, keypairGetEvents, runStatePrefix_bind, branch,
        getKeypair, getDev, hd, invariant, AmbientM.invariant, AmbientM.branch,
        liftWGPrefix, StateT.run_bind, StateT.run_pure] <;> rfl
    | some d =>
      cases hk : d.keypairs[i]? with
      | none => simp [keypairGetPrefix, keypairGetEvents, runStatePrefix_bind, branch,
          getKeypair, getDev, hd, hk, invariant, AmbientM.invariant, AmbientM.branch,
          liftWGPrefix, StateT.run_bind, StateT.run_pure] <;> rfl
      | some k =>
        by_cases hz : k.refcount = 0
        · simp [keypairGetPrefix, keypairGetEvents, runStatePrefix_bind, branch, branchCmp,
            getKeypair, getDev, hd, hk, hz, refcountIncNotZero, AmbientM.branch, AmbientM.branchCmp,
            liftWGPrefix, StateT.run_bind, StateT.run_pure] <;> rfl
        · by_cases ho : k.refcount + 1 ≥ 2 ^ 31
          all_goals have wrap : (2147483647 ≤ k.refcount) ↔ (k.refcount + 1 ≥ 2 ^ 31) := by omega
          all_goals simp [keypairGetPrefix, keypairGetEvents, runStatePrefix_bind, branch, branchCmp,
            getKeypair, getDev, hd, hk, hz, ho, wrap, refcountIncNotZero, unsupported,
            AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported, liftWGPrefix,
            StateT.run_bind, StateT.run_pure]
          all_goals try rw [map_eq_pure_bind, runStatePrefix_bind, setKeypairPrefix_run]
          all_goals try simp [setKeypair, modifyDev, hd, List.append_assoc]
          all_goals rfl

theorem keypairPutPrefix_events (kp : Option KeypairId) (now : Bool)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    (runStatePrefix (keypairPutPrefix kp now) w ambient h).2 = h ++ keypairPutEvents kp now w := by
  cases kp with
  | none => simp [keypairPutPrefix, keypairPutEvents, runStatePrefix_bind, liftWGPrefix, branch, AmbientM.branch,
      StateT.run_bind, StateT.run_pure] <;> rfl
  | some i =>
    cases hd : w.dev with
    | none => simp [keypairPutPrefix, keypairPutEvents, runStatePrefix_bind, branch,
        getKeypair, getDev, hd, invariant, AmbientM.invariant, AmbientM.branch,
        liftWGPrefix, StateT.run_bind, StateT.run_pure] <;> rfl
    | some d =>
      cases hk : d.keypairs[i]? with
      | none => simp [keypairPutPrefix, keypairPutEvents, runStatePrefix_bind, branch,
          getKeypair, getDev, hd, hk, invariant, AmbientM.invariant, AmbientM.branch,
          liftWGPrefix, StateT.run_bind, StateT.run_pure] <;> rfl
      | some k =>
        cases now <;> cases hp : k.peer <;>
          by_cases hz : k.refcount = 0 <;> by_cases ho : k.refcount = 1
        all_goals simp [keypairPutPrefix, keypairPutEvents, removeKeypairEntryPrefix,
          peerDerefPrefix, peerWordPrefix, runStatePrefix_bind, branch, branchCmp,
          getKeypair, getDev, hd, hk, hp, hz, ho, Nat.pos_iff_ne_zero, refcountDecAndTest, unsupported,
          setKeypair, modifyDev, removeKeypairIndex, indexRemove_eq, indexUnhash,
          Std.TreeMap.getElem?_insert, List.append_assoc, liftWGPrefix, liftM, monadLift, MonadLift.monadLift, liftIndex,
          AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported,
          StateT.run_bind, StateT.run_get, StateT.run_pure] <;> rfl

theorem keypairGetPrefix_run (kp : Option KeypairId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairGetPrefix kp) w ambient h = (((keypairGet kp).run w).run ambient, h ++ keypairGetEvents kp w) :=
  Prod.ext (keypairGetPrefix_erases kp w ambient h) (keypairGetPrefix_events kp w ambient h)

theorem keypairPutPrefix_run (kp : Option KeypairId) (now : Bool) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairPutPrefix kp now) w ambient h = (((keypairPut kp now).run w).run ambient, h ++ keypairPutEvents kp now w) :=
  Prod.ext (keypairPutPrefix_erases kp now w ambient h) (keypairPutPrefix_events kp now w ambient h)

/-- The zero-count path is case-complete: immediate unreference with a NULL
word stops before the write; otherwise the original count warning follows it.
Neither failure exposes a final native state or records a release. -/
theorem keypairPutPrefix_zero_failure (id : KeypairId) (now : Bool)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) (d : Device) (k : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs[id]? = some k) (hz : k.refcount = 0) :
    runStatePrefix (keypairPutPrefix (some id) now) w ambient h =
      (if now && k.peer.isNone then
        (.error (.outsideDomain
          s!"{Decision.keypairPutUnreferenceNow.info.file}:{Decision.keypairPutUnreferenceNow.info.line}"
          "entry->peer is NULL: the C dereferences it"),
          h ++ [.keypair (.read id k.internalId), .keypair (.read id k.internalId)])
      else
        (.error (.outsideDomain
          s!"{Decision.refcountSubNonpositive.info.file}:{Decision.refcountSubNonpositive.info.line}"
          "refcount_warn_saturate (use after free)"),
          h ++ ([.keypair (.read id k.internalId)] ++
            (if now then [.keypair (.read id k.internalId)] else []) ++
            [.keypair (.write id k.internalId)]))) := by
  rw [keypairPutPrefix_run]
  cases now <;> cases hp : k.peer <;>
    simp [keypairPut, keypairPutEvents, IndexOwner.peerDeref, IndexOwner.peerWord,
      branch, branchCmp, getKeypair, getDev, hd, hk, hp, hz, setKeypair,
      modifyDev, refcountDecAndTest, unsupported, indexRemove_eq, indexUnhash,
      List.append_assoc, liftM, monadLift, MonadLift.monadLift, liftIndex, AmbientM.branch, AmbientM.branchCmp,
      AmbientM.unsupported, StateT.run_bind, StateT.run_get, StateT.run_pure] <;> rfl

/-- A raw last-reference call with a NULL peer word stops after the decrement
and second owner read. There is no erase/release event. This source-level
conditional equation is not an initialized Runner counterexample. -/
theorem keypairPutPrefix_null_last_failure (id : KeypairId)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) (d : Device) (k : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs[id]? = some k)
    (hc : k.refcount = 1) (hp : k.peer = none) :
    runStatePrefix (keypairPutPrefix (some id) false) w ambient h =
      (.error (.outsideDomain
        s!"{Decision.keypairKrefPutReleased.info.file}:{Decision.keypairKrefPutReleased.info.line}"
        "entry->peer is NULL: the C dereferences it"),
        h ++ [.keypair (.read id k.internalId), .keypair (.write id k.internalId),
          .keypair (.read id k.internalId)]) := by
  rw [keypairPutPrefix_run]
  simp [keypairPut, keypairPutEvents, IndexOwner.peerDeref, IndexOwner.peerWord,
    branch, branchCmp, getKeypair, getDev, hd, hk, hp, hc, setKeypair,
    modifyDev, refcountDecAndTest, unsupported, indexRemove_eq, indexUnhash,
    Std.TreeMap.getElem?_insert, List.append_assoc, liftWGPrefix, liftM, monadLift, MonadLift.monadLift, liftIndex,
          AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported,
          StateT.run_bind, StateT.run_get, StateT.run_pure] <;> rfl

end Leanux.Proofs.WG.Lifetimes
