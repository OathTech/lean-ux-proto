import Leanux.Proofs.WG.Queues.StampedGro

/-! The original stamped GRO control flow with an event embedding and an
arbitrary product Stack observer. Source specializations retain every incoming
history and Stop; no callback success or history independence is assumed. -/
namespace Leanux.Proofs.WG.Queues.RxJoint.GroSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

variable {E F : Type}

def enterWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (e : Entry) : PrefixM E Unit := do
  emitPrefix (encode (.entered e))
  receiptObserved (stack e.tag.bytes) (fun r => encode (.completed e r))

def flushWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (entries : List Entry) : PrefixM E Unit :=
  entries.forM (enterWith encode stack)

def normalListWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (g : Gro) : PrefixM E Gro := do
  if g.rxCount == 0 then return g
  flushWith encode stack g.rxList
  return {g with rxList := [], rxCount := 0}

def normalOneWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (g : Gro) (e : Entry) (segs : Nat) : PrefixM E Gro := do
  let g := {g with rxList := g.rxList ++ [e], rxCount := g.rxCount + segs}
  if g.rxCount ≥ GRO_NORMAL_BATCH then normalListWith encode stack g else return g

def receiveWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit) (g : Gro) (e : Entry) : PrefixM E Gro := do
  match groNetwork e.tag.bytes with
  | none => normalOneWith encode stack g e 1
  | some (off, lengthFlush) =>
    match groTcpHeader e.tag.bytes off with
    | none => normalOneWith encode stack g e 1
    | some (thlen, len) =>
      let flags := (e.tag.bytes.getD (off + 13) 0).toNat
      match g.held with
      | [held] =>
        if groSameFlow held.tag.bytes e.tag.bytes off then
          if !groMergeRefused held.tag.bytes e.tag.bytes off thlen len then
            liftPrefix (unsupported "GRO coalesces two segments of one flow in one poll (skb_gro_receive)")
          let g ← normalOneWith encode stack {g with held := []} held 1
          if lengthFlush || groFinalFlush flags len then normalOneWith encode stack g e 1
          else return {g with held := [e]}
        else
          if lengthFlush || groFinalFlush flags len then normalOneWith encode stack g e 1
          else liftPrefix (unsupported "GRO holds a second TCP segment in one poll (the hash buckets' flush order)")
      | _ =>
        if lengthFlush || groFinalFlush flags len then normalOneWith encode stack g e 1
        else return {g with held := g.held ++ [e]}

def flushAllWith (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (gro : Gro) : PrefixM E Unit := do
  let mut g := gro
  for e in gro.held do g ← normalOneWith encode stack g e 1
  g := {g with held := []}
  _ ← normalListWith encode stack g

theorem enter_factor (e : Entry) :
    enter e = enterWith id (fun bytes => access (stackReceivePrefix bytes)) e := rfl

theorem flush_factor (entries : List Entry) :
    flush entries = flushWith id (fun bytes => access (stackReceivePrefix bytes)) entries := rfl

theorem normalList_factor (g : Gro) :
    normalList g = normalListWith id (fun bytes => access (stackReceivePrefix bytes)) g := rfl

theorem normalOne_factor (g : Gro) (e : Entry) (segs : Nat) :
    normalOne g e segs = normalOneWith id (fun bytes => access (stackReceivePrefix bytes)) g e segs := rfl

theorem receive_factor (g : Gro) (e : Entry) :
    receive g e = receiveWith id (fun bytes => access (stackReceivePrefix bytes)) g e := rfl

theorem flushAll_factor (g : Gro) :
    flushAll g = flushAllWith id (fun bytes => access (stackReceivePrefix bytes)) g := rfl

/-- Entry is emitted before the actual callback. A normal callback creates the
original full-product receipt; a Stop keeps exactly the callback's prefix. -/
theorem enter_run (encode : Event → E) (stack : List UInt8 → PrefixM E Unit)
    (e : Entry) (w : World) (h : List E) :
    runPrefix (enterWith encode stack e) w h =
      match runPrefix (stack e.tag.bytes) w (h ++ [encode (.entered e)]) with
      | (.error stop, t) => (.error stop, t)
      | (.ok (x, v), t) => (.ok (x, v), t ++ [encode (.completed e ⟨x, w, v⟩)]) := by
  simp only [enterWith, runPrefix_bind, runPrefix_emit, runPrefix_receiptObserved]
  cases hr : runPrefix (stack e.tag.bytes) w (h ++ [encode (.entered e)]) with
  | mk out t => cases out <;> rfl

/-- Retain, rather than erase, the exact successful receipt through projection.
Both observers run on the same product state and their actual input histories. -/
theorem receipt_projects {α : Type} (ρ : E → Option F)
    {a : PrefixM E α} {b : PrefixM F α}
    {receipt : RunWitness α → E} {receipt' : RunWitness α → F}
    (hr : ∀ r, ρ (receipt r) = some (receipt' r))
    (ha : ProjectsPrefix ρ id a b) :
    ProjectsPrefix ρ id (receiptObserved a receipt) (receiptObserved b receipt') := by
  intro w h
  rw [runPrefix_receiptObserved, runPrefix_receiptObserved, ha w h]
  cases he : runPrefix a w h with
  | mk out t =>
    cases out with
    | error stop => rfl
    | ok result =>
      rcases result with ⟨x, v⟩
      simp only [Except.map, id, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, hr]

variable (ρ : E → Option F) (encode : Event → E) (encode' : Event → F)
    (stack : List UInt8 → PrefixM E Unit) (stack' : List UInt8 → PrefixM F Unit)
    (he : ∀ e, ρ (encode e) = some (encode' e))
    (hs : ∀ bytes, ProjectsPrefix ρ id (stack bytes) (stack' bytes))

include he hs

theorem enter_projects (e : Entry) :
    ProjectsPrefix ρ id (enterWith encode stack e) (enterWith encode' stack' e) := by
  unfold enterWith
  apply projectsPrefix_bind ρ id id
  · simpa only [he, Option.elim_some] using projectsPrefix_emit (State := World) ρ (encode (.entered e))
  · intro _
    exact receipt_projects ρ (fun r => he (.completed e r)) (hs _)

theorem flush_projects (entries : List Entry) :
    ProjectsPrefix ρ id (flushWith encode stack entries) (flushWith encode' stack' entries) := by
  induction entries with
  | nil => exact projectsPrefix_pure ρ id ()
  | cons e rest ih =>
    simp only [flushWith, List.forM_eq_forM, List.forM_cons]
    exact projectsPrefix_bind ρ id id (enter_projects ρ encode encode' stack stack' he hs e) (fun _ => ih)

theorem normalList_projects (g : Gro) :
    ProjectsPrefix ρ id (normalListWith encode stack g) (normalListWith encode' stack' g) := by
  unfold normalListWith
  apply projectsPrefix_ite ρ _ id
  · intro _; exact projectsPrefix_pure ρ id g
  · intro _
    exact projectsPrefix_bind ρ id id (flush_projects ρ encode encode' stack stack' he hs g.rxList)
      (fun _ => projectsPrefix_pure ρ id _)

theorem normalOne_projects (g : Gro) (e : Entry) (segs : Nat) :
    ProjectsPrefix ρ id (normalOneWith encode stack g e segs) (normalOneWith encode' stack' g e segs) := by
  unfold normalOneWith
  apply projectsPrefix_ite ρ _ id
  · intro _; exact normalList_projects ρ encode encode' stack stack' he hs _
  · intro _; exact projectsPrefix_pure ρ id _

theorem receive_projects (g : Gro) (e : Entry) :
    ProjectsPrefix ρ id (receiveWith encode stack g e) (receiveWith encode' stack' g e) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact normalOne_projects ρ encode encode' stack stack' he hs _ _ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible apply projectsPrefix_bind ρ id id
    | (with_reducible intro x; try dsimp only [id])
    | (with_reducible split <;> try dsimp only [id])
  all_goals exact projectsPrefix_pure ρ id _

theorem flushAll_projects (g : Gro) :
    ProjectsPrefix ρ id (flushAllWith encode stack g) (flushAllWith encode' stack' g) := by
  unfold flushAllWith
  apply projectsPrefix_bind ρ id id
  · apply projectsPrefix_forIn ρ id
    intro e current
    exact projectsPrefix_bind ρ id (projectStep id)
      (normalOne_projects ρ encode encode' stack stack' he hs current e 1)
      (fun next => projectsPrefix_pure ρ (projectStep id) (.yield next))
  · intro current
    exact projectsPrefix_bind ρ id id
      (normalList_projects ρ encode encode' stack stack' he hs {current with held := []})
      (fun _ => projectsPrefix_pure ρ id ())

omit he hs

theorem enter_appends (ha : ∀ bytes, Appends (stack bytes)) (e : Entry) :
    Appends (enterWith encode stack e) := by
  unfold enterWith
  apply Appends.bind (show Appends (emitPrefix (encode (.entered e))) from fun _ _ => ⟨_, rfl⟩)
  intro _
  exact (ha e.tag.bytes).receiptObserved

theorem flush_appends (ha : ∀ bytes, Appends (stack bytes)) (entries : List Entry) :
    Appends (flushWith encode stack entries) := by
  induction entries with
  | nil => exact Appends.pure ()
  | cons e rest ih =>
    simp only [flushWith, List.forM_eq_forM, List.forM_cons]
    exact (enter_appends encode stack ha e).bind (fun _ => ih)

theorem normalList_appends (ha : ∀ bytes, Appends (stack bytes)) (g : Gro) :
    Appends (normalListWith encode stack g) := by
  unfold normalListWith
  split
  · exact Appends.pure _
  · exact (flush_appends encode stack ha g.rxList).bind (fun _ => Appends.pure _)

theorem normalOne_appends (ha : ∀ bytes, Appends (stack bytes))
    (g : Gro) (e : Entry) (segs : Nat) : Appends (normalOneWith encode stack g e segs) := by
  unfold normalOneWith
  dsimp only
  split
  · exact normalList_appends encode stack ha _
  · exact Appends.pure _

theorem receive_appends (ha : ∀ bytes, Appends (stack bytes)) (g : Gro) (e : Entry) :
    Appends (receiveWith encode stack g e) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact normalOne_appends encode stack ha _ _ _
    | with_reducible exact Appends.pure _
    | with_reducible exact Appends.lift _
    | with_reducible apply Appends.bind
    | (with_reducible intro x; try dsimp only [id])
    | (with_reducible split <;> try dsimp only [id])

theorem flushAll_appends (ha : ∀ bytes, Appends (stack bytes)) (g : Gro) :
    Appends (flushAllWith encode stack g) := by
  unfold flushAllWith
  apply Appends.bind
  · apply Appends.forIn
    intro e current
    exact (normalOne_appends encode stack ha current e 1).bind (fun next => Appends.pure (ForInStep.yield next))
  · intro current
    exact (normalList_appends encode stack ha {current with held := []}).bind (fun _ => Appends.pure ())

end Leanux.Proofs.WG.Queues.RxJoint.GroSource
