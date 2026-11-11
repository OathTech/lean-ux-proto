import C1WitnessScene
import C1Joined

/-! Result C1, open proposition `WitnessHolds`: the mirror's four runs.

The kernel cannot evaluate the mirror's `insert` as it stands: the one
obstacle is the `while` loop of `AmbientM.hiddenAlloc` (Lean's `Loop` is
opaque to reduction). Package 1 already shows that loop to run its body
once at a site that consumes one record (`hiddenAllocCopy_once`). So `add`
is copied here with the allocation at such a site written without the loop
(`addFree`, the text of `Leanux.WG.add` otherwise unchanged), the copy is
proved equal to the mirror's `add`, and the four runs are then closed
evaluations (`decide +kernel`). Nothing here changes the mirror. -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1 Binary.Statements.C1.Proof

/-! ## `add` without the loop -/

/-- The mirror's private placeholder encounter (package 1's `hiddenAlloc_copy`
names it only existentially). It is never run here: the world has records. -/
noncomputable def placeholder : AllocSite → AmbientM Bool := Classical.choose hiddenAlloc_copy

theorem hiddenAlloc_eq (s : AllocSite) : AmbientM.hiddenAlloc s = hiddenAllocCopy placeholder s :=
  Classical.choose_spec hiddenAlloc_copy s

/-- `AmbientM.hiddenAlloc` at a site that consumes exactly one record: the
right-hand side of package 1's `hiddenAllocCopy_once`. -/
noncomputable def hiddenAllocFree (s : AllocSite) : AmbientM Bool := do
  let w ← get
  let placeholders := w.hidden.isNone && w.hiddenPlaceholders
  if !placeholders && !w.allocArmed.contains s.info.label then return true
  (if placeholders then placeholder s else allocRecordCopy s)

/-- `Leanux.WG.allocNode` over `hiddenAllocFree`, text otherwise unchanged. -/
noncomputable def allocNodeFree (site : AllocSite) (n : AipNode) : AipM (Option NodeId) := do
  if !(← (monadLift (hiddenAllocFree site) : AipM Bool)) then return none
  let id := (← get).nextNode
  modify fun s => { s with nextNode := id + 1, nodes := s.nodes.insert id n }
  return some id

theorem allocNode_free (site : AllocSite) (n : AipNode) (count : site.info.count = .exact 1) :
    allocNode site n = allocNodeFree site n := by
  unfold allocNode allocNodeFree hiddenAlloc
  rw [hiddenAlloc_eq, hiddenAllocCopy_once _ _ count]
  rfl

/-- Copy of the mirror's `Leanux.WG.add` (Leanux/WG/AllowedIps.lean), text
unchanged but for `allocNodeFree` in place of `allocNode` at its three sites. -/
noncomputable def addFree (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : WG.M Int := do
  -- `unlikely(cidr > bits || !peer)`
  if ← branchCmp .addCidrTooLong (cidr > bits) cidr bits then return -EINVAL
  if ← branch .addNoPeer peer.isNone then return -EINVAL
  let some pid := peer | invariant "unreachable"
  let trie ← slotGet root
  if ← branch .addEmptyTrie trie.isNone then
    let some id ← (do
        let r ← allocNodeFree .allocNode190 (newNode key cidr bits (some pid))
        if ← branch .addRootNoMem r.isNone then return none
        pure r) | return -ENOMEM
    listAddTail pid id
    connectNode root id
    return 0
  let (placed, exact) ← nodePlacement trie key cidr bits
  if ← branch .addExact exact then
    let some id := placed | invariant "exact placement without a node"
    setNode id { (← getNode id) with peer := some pid }
    listDel id              -- list_move_tail
    listAddTail pid id
    return 0
  let newnodeAlloc ← allocNodeFree .allocNode205 (newNode key cidr bits (some pid))
  if ← branch .addNewnodeNoMem newnodeAlloc.isNone then return -ENOMEM
  let some newnode := newnodeAlloc | invariant "unreachable"
  listAddTail pid newnode
  let down ← do
    if ← branch .addNoParentNode placed.isNone then slotGet root
    else
      let some node := placed | invariant "unreachable"
      let bit ← choose (← getNode node) key
      let down ← (← getNode node).bitAt bit
      if ← branch .addNoDown down.isNone then
        connectNode (.child node bit) newnode
        return 0
      pure down
  let some downId := down | invariant "add: no node below the placement"
  let common ← commonBits (← getNode downId) key bits
  let cidr := min cidr common   -- branch-free
  let parent := placed
  -- the compiler compares `cidr` with `common` rather than the source operands
  if ← branch .addNewnodeCoversDown ((← getNode newnode).cidr == cidr) then
    chooseAndConnectNode newnode downId
    if ← branch .addNewnodeAtRoot parent.isNone then connectNode root newnode
    else if let some p := parent then chooseAndConnectNode p newnode
    return 0
  let nodeAlloc ← allocNodeFree .allocNode234 (newNode (← getNode newnode).bits cidr bits none)
  if ← branch .addIntermediateNoMem nodeAlloc.isNone then
    listDel newnode
    freeNode newnode
    return -ENOMEM
  let some node := nodeAlloc | invariant "unreachable"
  chooseAndConnectNode node downId
  chooseAndConnectNode node newnode
  if ← branch .addIntermediateAtRoot parent.isNone then connectNode root node
  else if let some p := parent then chooseAndConnectNode p node
  return 0

theorem add_free (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    add root bits key cidr peer = addFree root bits key cidr peer := by
  unfold add addFree
  simp only [allocNode_free _ _ (show AllocSite.allocNode190.info.count = .exact 1 from rfl),
    allocNode_free _ _ (show AllocSite.allocNode205.info.count = .exact 1 from rfl),
    allocNode_free _ _ (show AllocSite.allocNode234.info.count = .exact 1 from rfl)]
  rfl

/-- Copy of the mirror's `Leanux.WG.insert` over `addFree`. -/
noncomputable def insertFree (family : Nat) (addr cidr : Nat) (peer : PeerId) : WG.M Int := do
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  if family == 4 then addFree .root4 32 addr cidr (some peer)
  else addFree .root6 128 addr cidr (some peer)

theorem insert_free (family addr cidr : Nat) (peer : PeerId) :
    WG.insert family addr cidr peer = insertFree family addr cidr peer := by
  unfold WG.insert insertFree
  simp only [add_free]

/-! ## The four runs -/

def answerOf {α : Type} (r : Except Stop (α × World)) : Option α :=
  match r with
  | .ok (a,_) => some a
  | _ => none

def worldOf {α : Type} (r : Except Stop (α × World)) : World :=
  match r with
  | .ok (_,w) => w
  | _ => world

theorem ok_of_answer {α : Type} {r : Except Stop (α × World)} {a : α} (answer : answerOf r = some a) :
    r = .ok (a,worldOf r) := by
  match r, answer with
  | .ok (b,w), answer =>
    cases Option.some.inj answer
    rfl

/-- The worlds after the root insertion, the two-allocation insertion and the
rolled-back insertion, and after the lookup. -/
noncomputable def world1 : World := worldOf ((liftWG (insertFree 4 0x0a000000 24 0)).run world)
noncomputable def world2 : World := worldOf ((liftWG (insertFree 4 0x0b000001 32 1)).run world1)
noncomputable def world3 : World := worldOf ((liftWG (insertFree 4 0x0c000001 32 0)).run world2)

/-- The root the lookup starts from: the mirror's `root4` after the three insertions. -/
noncomputable def root3 : Option NodeId := world3.wg.dev.bind fun d => d.peerAllowedips.root4

noncomputable def world4 : World := worldOf ((Source.lookup root3 32 0x0a000005).run world3)

theorem world_armed : armed world = true := by decide +kernel

theorem world_hidden : world.ambient.hidden = some (five ++ []) := rfl

theorem world_sites : ∀ record ∈ ([] : List HiddenRecord), record.site ∈ allocSites.map (·.2) :=
  fun _ member => nomatch member

/-- An insertion into the empty table: the mirror returns 0. -/
theorem run_first : (liftWG (WG.insert 4 0x0a000000 24 0)).run world = .ok (0,world1) := by
  rw [insert_free]
  exact ok_of_answer (by decide +kernel)

/-- An insertion that allocates twice (the new node and the intermediate node): 0. -/
theorem run_second : (liftWG (WG.insert 4 0x0b000001 32 1)).run world1 = .ok (0,world2) := by
  rw [insert_free]
  exact ok_of_answer (by decide +kernel)

/-- A record as its two fields (`HiddenRecord` has no decidable equality). -/
def fields (records : Option (List HiddenRecord)) : Option (List (Nat × List UInt8)) :=
  records.map (·.map fun record => (record.site,record.bytes))

theorem fields_injective : ∀ (records expected : List HiddenRecord),
    records.map (fun record => (record.site,record.bytes)) =
      expected.map (fun record => (record.site,record.bytes)) → records = expected
  | [], [], _ => rfl
  | [], _ :: _, same => nomatch same
  | _ :: _, [], same => nomatch same
  | ⟨site,bytes⟩ :: rest, ⟨site',bytes'⟩ :: others, same => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at same
    obtain ⟨⟨rfl,rfl⟩,tail⟩ := same
    rw [fields_injective rest others tail]

theorem records_of_fields {found : Option (List HiddenRecord)} {expected : List HiddenRecord}
    (same : fields found = fields (some expected)) : found = some expected := by
  cases found with
  | none => cases same
  | some records => exact congrArg some (fields_injective records expected (Option.some.inj same))

theorem hidden_second : world2.ambient.hidden = some ([outcome 78 true, outcome 79 false] ++ []) :=
  records_of_fields (by decide +kernel)

/-- An insertion whose second allocation is refused: the rollback, `-ENOMEM`. -/
theorem run_third : (liftWG (WG.insert 4 0x0c000001 32 0)).run world2 = .ok (-12,world3) := by
  rw [insert_free]
  exact ok_of_answer (by decide +kernel)

theorem hidden_third : world3.ambient.hidden = some [] := records_of_fields (by decide +kernel)

theorem bind_of {α β : Type} {o : Option α} {d : α} (f : α → Option β) (present : o = some d) :
    f d = o.bind f := by
  subst present
  rfl

/-- The device after the three insertions. -/
theorem device_third : ∃ d, world3.wg.dev = some d ∧ d.peerAllowedips.root4 = root3 := by
  have present : world3.wg.dev.isSome = true := by decide +kernel
  have some_of : ∀ o : Option Device, o.isSome = true → ∃ d, o = some d :=
    fun _ h => Option.isSome_iff_exists.mp h
  obtain ⟨d,device⟩ := some_of _ present
  refine ⟨d,device,?_⟩
  rw [root3]
  exact bind_of (fun d : Device => d.peerAllowedips.root4) device

/-- A lookup of 10.0.0.5 finds peer 0. -/
theorem run_lookup : (Source.lookup root3 32 0x0a000005).run world3 = .ok (some 0,world4) :=
  ok_of_answer (by decide +kernel)

#print axioms run_first
#print axioms run_second
#print axioms run_third
#print axioms run_lookup
#print axioms hidden_second
#print axioms hidden_third
end Binary.Statements.C1.Witness
