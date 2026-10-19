import Leanux.Proofs.WG.Packets.NativeTransmit

/-! Event-generic factors of the already defined transmit capture and tail.
Only the receipt constructor and supplied observers vary; the actual front
and tail bodies remain in TxObservedFront. -/
namespace Leanux.Proofs.WG.TransmitJoint.Source
open Leanux Leanux.WG Leanux.Proofs.Logged Queues

/-- Capture a supplied native observer once; emit only its completed splice. -/
def frontWith {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) : WGPrefix E (Except Int PeerId) := do
  let r ← captureWGObserved front
  match r.value with
  | .error _ => pure r.value
  | .ok _ => emitStatePrefix (receipt r); pure r.value

def transmitWith {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (tail : PeerId → WGPrefix E Int) : WGPrefix E Int := do
  match ← frontWith receipt front with
  | .error err => pure err
  | .ok pid => tail pid

theorem observeFront_factor (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId)) :
    TransmitJoint.observeFront family addr packets mtu front =
      frontWith (fun r => Event.transmit ⟨family,addr,packets,mtu,r⟩) (old front) := rfl

theorem transmitWith_factor (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int) :
    TransmitJoint.transmitWith family addr packets mtu front tail =
      transmitWith (fun r => Event.transmit ⟨family,addr,packets,mtu,r⟩)
        (old front) (fun pid => old (tail pid)) := rfl

theorem frontWith_run {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (w : WGWorld) (ambient : Ambient) (h : List E) :
    runWGPrefix (frontWith receipt front) w ambient h =
      match runWGPrefix front w ambient h with
      | (.error stop,hist) => (.error stop,hist)
      | (.ok ((value,v),after),hist) =>
        (.ok ((value,v),after), match value with
          | .error _ => hist
          | .ok _ => hist ++ [receipt ⟨value,w,v,ambient,after⟩]) := by
  change runStatePrefix (frontWith receipt front) w ambient h = _
  rw [frontWith,runStatePrefix_bind]
  have captured := runWGPrefix_captureWGObserved front w ambient h
  simp only [runWGPrefix] at captured
  rw [captured]
  simp only [runWGPrefix]
  cases run : runStatePrefix front w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out => rcases out with ⟨⟨value,v⟩,after⟩; cases value <;> rfl

theorem frontWith_projects {E F : Type} (ρ : E → Option F)
    (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (lower : WGPrefix F (Except Int PeerId))
    (quiet : ∀ r, ρ (receipt r) = none) (hf : StateProjectsPrefix ρ id front lower) :
    StateProjectsPrefix ρ id (frontWith receipt front) lower := by
  intro w ambient h
  have projected := hf w ambient h
  change runWGPrefix lower w ambient (h.filterMap ρ) =
    ((runWGPrefix (frontWith receipt front) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix (frontWith receipt front) w ambient h).2.filterMap ρ)
  change runWGPrefix lower w ambient (h.filterMap ρ) =
    ((runWGPrefix front w ambient h).1.map (fun ((x,v),a) => ((x,v),a)),
      (runWGPrefix front w ambient h).2.filterMap ρ) at projected
  rw [frontWith_run]
  cases run : runWGPrefix front w ambient h with
  | mk result hist =>
    cases result with
    | error stop => simpa only [run] using projected
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      cases value <;> simpa only [run,List.filterMap_append,List.filterMap_cons,
        quiet,List.filterMap_nil,List.append_nil] using projected

theorem transmitWith_projects {E F : Type} (ρ : E → Option F)
    (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (lower : WGPrefix F (Except Int PeerId))
    (tail : PeerId → WGPrefix E Int) (lowerTail : PeerId → WGPrefix F Int)
    (quiet : ∀ r, ρ (receipt r) = none) (hf : StateProjectsPrefix ρ id front lower)
    (ht : ∀ pid, StateProjectsPrefix ρ id (tail pid) (lowerTail pid)) :
    StateProjectsPrefix ρ id (transmitWith receipt front tail)
      (do match ← lower with | .error err => pure err | .ok pid => lowerTail pid) := by
  unfold transmitWith
  apply StateProjectsPrefix.bind ρ id id (frontWith_projects ρ receipt front lower quiet hf)
  intro result
  cases result with
  | error err => intro w; exact projectsPrefix_pure ρ (Prod.map id id) (err,w)
  | ok pid => exact ht pid

theorem frontWith_appends {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (hf : StateAppends front) :
    StateAppends (frontWith receipt front) := by
  unfold frontWith
  apply StateAppends.bind hf.captureWGObserved
  intro r
  cases r.value with
  | error err => exact StateAppends.pure _
  | ok pid =>
    apply StateAppends.bind
    · intro w ambient h; exact ⟨[_],rfl⟩
    · intro _; exact StateAppends.pure _

theorem transmitWith_appends {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (tail : PeerId → WGPrefix E Int)
    (hf : StateAppends front) (ht : ∀ pid, StateAppends (tail pid)) :
    StateAppends (transmitWith receipt front tail) := by
  unfold transmitWith
  apply StateAppends.bind (frontWith_appends receipt front hf)
  intro result
  cases result with
  | error err => exact StateAppends.pure _
  | ok pid => exact ht pid

/-- The native front is evaluated once. Its successful splice receipt is
already in the journal passed to the original tail, including a stopped tail. -/
theorem transmitWith_run {E : Type} (receipt : WGRunWitness (Except Int PeerId) → E)
    (front : WGPrefix E (Except Int PeerId)) (tail : PeerId → WGPrefix E Int)
    (w : WGWorld) (ambient : Ambient) (h : List E) :
    runWGPrefix (transmitWith receipt front tail) w ambient h =
      match runWGPrefix front w ambient h with
      | (.error stop,hist) => (.error stop,hist)
      | (.ok ((.error err,v),after),hist) => (.ok ((err,v),after),hist)
      | (.ok ((.ok pid,v),after),hist) =>
        runWGPrefix (tail pid) v after (hist ++ [receipt ⟨.ok pid,w,v,ambient,after⟩]) := by
  change runStatePrefix (transmitWith receipt front tail) w ambient h = _
  rw [transmitWith,runStatePrefix_bind]
  have captured := frontWith_run receipt front w ambient h
  simp only [runWGPrefix] at captured
  rw [captured]
  simp only [runWGPrefix]
  cases run : runStatePrefix front w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out => rcases out with ⟨⟨value,v⟩,after⟩; cases value <;> rfl

end Leanux.Proofs.WG.TransmitJoint.Source
