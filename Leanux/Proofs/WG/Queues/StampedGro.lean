import Leanux.Proofs.Logged.ProjectsUnderTo
import Leanux.Proofs.Logged.Capture
import Leanux.Proofs.WG.Queues.RxPollGro
import Leanux.Proofs.WG.Lifetimes.BatchNapi
import Leanux.Proofs.WG.Queues.RxDispositionReceipts

/-! One journal carries original lifetime accesses and captured receive
identities through the original GRO lists. Entry precedes the actual stack
callback, including a callback which Stops. A receipt is appended only after
its actual normal return. No residency of held payloads is asserted: their
original packet storage may already have been freed. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

structure Entry where
  tag : GroEntry
  stamp : PacketStamp
  origin : Option RxDisposition.ConsumeReceipt := none

inductive Event where
  | access (event : LifetimeEvent)
  | removed (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
  | checkedState (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
      (packet : RxPacket) (run : RunWitness Bool)
  | checkedCounter (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
      (packet : RxPacket) (run : RunWitness Bool)
  | checkedEndpoint (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
      (packet : RxPacket) (run : RunWitness (Option Endpoint))
  | consumed (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
      (receipt : RxDisposition.ConsumeReceipt)
  | buffered (entry : Entry)
  | entered (entry : Entry)
  | completed (entry : Entry) (witness : RunWitness Unit)

def accessEvent : Event → Option LifetimeEvent | .access e => some e | _ => none
def groEvent : Event → Option GroEvent
  | .access _ => none
  | .removed n id _ => some (.removed n id)
  | .buffered e => some (.buffered e.tag)
  | .entered e => some (.entered e.tag)
  | .completed _ _ => none
  | .consumed _ _ _ _ => none
  | .checkedState .. | .checkedCounter .. | .checkedEndpoint .. => none

abbrev Obs := PrefixM Event
def access (a : PrefixM LifetimeEvent α) : Obs α := focusPrefix Event.access accessEvent a

theorem access_erases (he : ErasesPrefix a original) : ErasesPrefix (access a) original :=
  focusPrefix_erases _ _ he

theorem access_gro (he : ErasesPrefix a original) :
    ProjectsPrefix groEvent id (access a) (liftPrefix original) :=
  projectsPrefix_focus_other _ _ _ (fun _ => rfl) he

theorem access_projects (ha : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe a) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (access a) a :=
  ha.projects_focus _ _ (fun _ => rfl)

structure Gro where
  rxList : List Entry := []
  rxCount : Nat := 0
  held : List Entry := []

def Gro.forget (g : Gro) : TaggedGro :=
  ⟨g.rxList.map Entry.tag, g.rxCount, g.held.map Entry.tag⟩
def Gro.erase (g : Gro) : GroState := g.forget.erase

def enter (e : Entry) : Obs Unit := do
  emitPrefix (.entered e)
  receiptObserved (access (stackReceivePrefix e.tag.bytes)) (Event.completed e)

def flush (entries : List Entry) : Obs Unit := entries.forM enter

def normalList (g : Gro) : Obs Gro := do
  if g.rxCount == 0 then return g
  flush g.rxList
  return {g with rxList := [], rxCount := 0}

def normalOne (g : Gro) (e : Entry) (segs : Nat) : Obs Gro := do
  let g := {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  if g.rxCount ≥ GRO_NORMAL_BATCH then normalList g else return g

def receive (g : Gro) (e : Entry) : Obs Gro := do
  if groTakenAtOnce e.tag.bytes then normalOne g e 1
  else
    if !g.held.isEmpty then
      liftPrefix (unsupported "GRO holds a second TCP segment in one poll (coalescing, or the hash buckets' flush order)")
    return {g with held := g.held ++ [e]}

def flushAll (gro : Gro) : Obs Unit := do
  let mut g := gro
  for e in gro.held do g ← normalOne g e 1
  g := {g with held := []}
  _ ← normalList g

theorem enter_gro (e : Entry) :
    ProjectsPrefix groEvent id (enter e) (enterGro e.tag) := by
  unfold enter enterGro
  exact projectsPrefix_bind groEvent id id (projectsPrefix_emit _ _)
    (fun _ => receiptObserved_projects (fun _ => rfl)
      (access_gro (stackReceivePrefix_erases _)))

theorem flush_gro (entries : List Entry) :
    ProjectsPrefix groEvent id (flush entries) (flushGro (entries.map Entry.tag)) := by
  induction entries with
  | nil => exact projectsPrefix_pure _ id _
  | cons e rest ih =>
    simp only [flush, flushGro, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    exact projectsPrefix_bind groEvent id id (enter_gro e) (fun _ => ih)

theorem normalList_gro (g : Gro) :
    ProjectsPrefix groEvent Gro.forget (normalList g) (groNormalListTagged g.forget) := by
  unfold normalList groNormalListTagged
  dsimp only [Gro.forget]
  apply projectsPrefix_ite
  all_goals intro h
  · exact projectsPrefix_pure _ _ _
  · exact projectsPrefix_bind groEvent id Gro.forget (flush_gro _)
      (fun _ => projectsPrefix_pure _ _ _)

theorem normalOne_gro (g : Gro) (e : Entry) (segs : Nat) :
    ProjectsPrefix groEvent Gro.forget (normalOne g e segs)
      (groNormalOneTagged g.forget e.tag segs) := by
  unfold normalOne groNormalOneTagged
  dsimp only [Gro.forget]
  split
  · simpa [Gro.forget, List.map_append] using
      normalList_gro {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  · simpa [Gro.forget, List.map_append] using
      projectsPrefix_pure groEvent Gro.forget {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}

theorem receive_gro (g : Gro) (e : Entry) :
    ProjectsPrefix groEvent Gro.forget (receive g e) (napiGroReceiveTagged g.forget e.tag) := by
  unfold receive napiGroReceiveTagged
  simp only [Gro.forget, List.isEmpty_map]
  split
  · exact normalOne_gro g e 1
  · split
    · apply projectsPrefix_bind groEvent id Gro.forget (projectsPrefix_lift _ _)
      intro _
      simpa [Gro.forget, List.map_append] using
        projectsPrefix_pure groEvent Gro.forget {g with held := g.held ++ [e]}
    · simpa [Gro.forget, List.map_append] using
        projectsPrefix_pure groEvent Gro.forget {g with held := g.held ++ [e]}

theorem flushAll_gro (g : Gro) :
    ProjectsPrefix groEvent id (flushAll g) (napiGroFlushAllTagged g.forget) := by
  unfold flushAll napiGroFlushAllTagged
  apply projectsPrefix_bind groEvent Gro.forget id
  · apply projectsPrefix_forIn_map groEvent Gro.forget Entry.tag
    intro e g
    exact projectsPrefix_bind groEvent Gro.forget (projectStep Gro.forget)
      (normalOne_gro g e 1) (fun g => projectsPrefix_pure _ _ (ForInStep.yield g))
  · intro g
    apply projectsPrefix_bind groEvent Gro.forget id (normalList_gro {g with held := []})
    intro _
    exact projectsPrefix_pure _ id ()

theorem stack_allocation (bytes : List UInt8) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (stackReceivePrefix bytes) :=
  stackReceivePrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩ bytes

theorem stackFlush_allocation (bytes : List (List UInt8)) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (stackFlushPrefix bytes) :=
  stackFlushPrefix_preserves (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) ⟨fun P => (allocationWgXmit.errors P).liftWGObserver⟩ bytes

theorem enter_access (e : Entry) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (enter e) (stackReceivePrefix e.tag.bytes) := by
  exact projectsUnder_emit_bind _ rfl
    (receiptObserved_projectsUnder (fun _ => rfl) (access_projects (stack_allocation _)))

theorem flush_access (entries : List Entry) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (flush entries)
      (stackFlushPrefix (entries.map fun e => e.tag.bytes)) := by
  induction entries with
  | nil => exact projectsUnder_pure _ _
  | cons e rest ih =>
    simp only [flush, stackFlushPrefix, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    exact projectsUnder_bind (enter_access e) (stack_allocation _) (fun _ => ih)

theorem normalList_access (g : Gro) :
    ProjectsUnderTo (fun h w => AllocationInv h w.wg) accessEvent Gro.erase (normalList g)
      (groNormalListPrefix stackFlushPrefix g.erase) := by
  unfold normalList groNormalListPrefix
  dsimp only [Gro.erase, Gro.forget, TaggedGro.erase]
  apply projectsUnderTo_ite
  all_goals intro h
  · exact projectsUnderTo_pure _ _ _
  · apply projectsUnderTo_bind accessEvent id Gro.erase
    · simpa [List.map_map, Function.comp_def] using (flush_access g.rxList).to_mapped
    · exact stackFlush_allocation _
    · intro _; exact projectsUnderTo_pure _ _ _

theorem normalOne_access (g : Gro) (e : Entry) (segs : Nat) :
    ProjectsUnderTo (fun h w => AllocationInv h w.wg) accessEvent Gro.erase (normalOne g e segs)
      (groNormalOnePrefix stackFlushPrefix g.erase e.tag.bytes segs) := by
  unfold normalOne groNormalOnePrefix
  dsimp only [Gro.erase, Gro.forget, TaggedGro.erase]
  split
  · simpa [Gro.erase, Gro.forget, TaggedGro.erase, List.map_append] using
      normalList_access {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  · simpa [Gro.erase, Gro.forget, TaggedGro.erase, List.map_append] using
      projectsUnderTo_pure accessEvent Gro.erase {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}

theorem receive_access (g : Gro) (e : Entry) :
    ProjectsUnderTo (fun h w => AllocationInv h w.wg) accessEvent Gro.erase (receive g e)
      (napiGroReceivePrefix stackFlushPrefix g.erase e.tag.bytes) := by
  unfold receive napiGroReceivePrefix
  simp only [Gro.erase, Gro.forget, TaggedGro.erase, List.isEmpty_map]
  split
  · exact normalOne_access g e 1
  · split
    · apply projectsUnderTo_bind accessEvent id Gro.erase (projectsPrefix_lift _ _).underTo
      · exact Lifetimes.allocation_store World.wg _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))
      · intro _
        simpa [Gro.erase, Gro.forget, TaggedGro.erase, List.map_append] using
          projectsUnderTo_pure accessEvent Gro.erase {g with held := g.held ++ [e]}
    · simpa [Gro.erase, Gro.forget, TaggedGro.erase, List.map_append] using
        projectsUnderTo_pure accessEvent Gro.erase {g with held := g.held ++ [e]}

theorem flushAll_access (gro : Gro) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) accessEvent (flushAll gro)
      (napiGroFlushAllPrefix stackFlushPrefix gro.erase) := by
  apply ProjectsUnderTo.identity
  unfold flushAll napiGroFlushAllPrefix
  apply projectsUnderTo_bind accessEvent Gro.erase id
  · rw [show gro.erase.held = gro.held.map (fun e => e.tag.bytes) by
      simp [Gro.erase, Gro.forget, TaggedGro.erase, List.map_map]]
    apply projectsUnderTo_forIn_map accessEvent Gro.erase (fun e : Entry => e.tag.bytes)
    · intro bytes g
      exact PrefixPreserves.bind
        (groNormalOnePrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation g bytes 1)
        (fun g => PrefixPreserves.pure (fun _ _ hi => hi.safe) (ForInStep.yield g))
    · intro e g
      apply projectsUnderTo_bind accessEvent Gro.erase (projectStep Gro.erase) (normalOne_access g e 1)
      · exact groNormalOnePrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _ _ _
      · intro g; exact projectsUnderTo_pure _ _ (ForInStep.yield g)
  · apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    intro bytes g
    exact PrefixPreserves.bind
      (groNormalOnePrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation g bytes 1)
      (fun g => PrefixPreserves.pure (fun _ _ hi => hi.safe) (ForInStep.yield g))
  · intro g
    apply projectsUnderTo_bind accessEvent Gro.erase id (normalList_access {g with held := []})
    · exact groNormalListPrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _
    · intro _; exact projectsUnderTo_pure _ id ()

end Leanux.Proofs.WG.Queues.RxJoint
