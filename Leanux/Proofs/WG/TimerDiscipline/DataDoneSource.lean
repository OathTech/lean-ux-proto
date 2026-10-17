import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do Campaign2
variable {α β : Type}

def dataDoneStep (pid : PeerId) (id : SkbId) (dataSent : Bool) : WG.M (ForInStep Bool) := do
  let skb ← getTxSkb id
  _ ← branch .doneSkbIterate true
  let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← sendSkbToPeer pid skb.bytes skb.ds
  let qualifies ← WG.andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive)
  if qualifies then return .yield true
  return .yield dataSent


def dataDoneFinish (pid : PeerId) (dataSent : Bool) : WG.M Unit := do
  _ ← branch .doneSkbIterate false
  if ← branch .doneDataSent dataSent then timersDataSent pid
  keepKeyFresh pid


def dataDoneSource (pid : PeerId) (item : List SkbId) : WG.M Unit := do
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let dataSent ← forIn item false (dataDoneStep pid)
  dataDoneFinish pid dataSent


theorem dataDoneSource_eq (pid : PeerId) (item : List SkbId) :
    dataDoneSource pid item = createDataDone pid item := by
  rfl


def dataDoneObservedStep (pid : PeerId) (id : SkbId) (dataSent : Bool) :
    WG.M (ForInStep Bool × DataDoneItem) := do
  let skb ← getTxSkb id
  _ ← branch .doneSkbIterate true
  let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← sendSkbToPeer pid skb.bytes skb.ds
  let qualifies ← WG.andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive)
  if qualifies then return (.yield true, ⟨id, skb, sent, qualifies⟩)
  return (.yield dataSent, ⟨id, skb, sent, qualifies⟩)


theorem dataDoneObservedStep_erase (pid : PeerId) (id : SkbId) (before : Bool) :
    (do let result ← dataDoneObservedStep pid id before; pure result.1) = dataDoneStep pid id before := by
  simp only [dataDoneObservedStep, dataDoneStep, bind_assoc]
  congr 1
  funext packet
  congr 1
  funext ignored
  congr 1
  funext sent
  congr 1
  funext qualifies
  cases qualifies <;> rfl


def dataDoneObservedItems (pid : PeerId) : List SkbId → Bool → WG.M (Bool × List DataDoneItem)
  | [], before => pure (before, [])
  | id :: rest, before => do
    let (next, observation) ← dataDoneObservedStep pid id before
    match next with
    | .done flag => return (flag, [observation])
    | .yield flag =>
      let (final, tail) ← dataDoneObservedItems pid rest flag
      return (final, observation :: tail)


theorem dataDoneObservedItems_erase (pid : PeerId) (items : List SkbId) (before : Bool) :
    (do let result ← dataDoneObservedItems pid items before; pure result.1) =
      forIn items before (dataDoneStep pid) := by
  induction items generalizing before with
  | nil => rfl
  | cons id rest ih =>
    simp only [dataDoneObservedItems, List.forIn_cons]
    rw [← dataDoneObservedStep_erase pid id before]
    simp only [bind_assoc, pure_bind]
    congr 1
    funext pair
    rcases pair with ⟨next, observation⟩
    cases next with
    | done flag => rfl
    | yield flag =>
      simp only [bind_assoc, pure_bind]
      exact ih flag


def dataDoneCapture (operation : Leanux.M Unit) (probe : Leanux.M α) : Leanux.M (DataDoneTimerCut α) := do
  let before ← Campaign2.Product.read
  let value ← observed operation probe
  let after ← Campaign2.Product.read
  return ⟨before, value.1, after⟩


theorem dataDoneCapture_erase (operation : Leanux.M Unit) (probe : Leanux.M α) :
    (do let _ ← dataDoneCapture operation probe; pure ()) = operation := by
  calc
    _ = (do let value ← observed operation probe; pure value.2) := by
      funext entry
      change (((observed operation probe).run entry >>= fun out =>
        Except.ok (DataDoneTimerCut.mk (Product.snapshot entry) out.1.1 (Product.snapshot out.2), out.2))
          >>= fun out => Except.ok ((), out.2)) =
        ((observed operation probe).run entry >>= fun out => Except.ok (out.1.2, out.2))
      cases run : (observed operation probe).run entry with
      | error err => rfl
      | ok pair => rcases pair with ⟨⟨value, u⟩, final⟩; cases u; rfl
    _ = operation := observed_erase operation probe


theorem dataDoneCapture_bind (operation : Leanux.M Unit) (probe : Leanux.M α) (next : Leanux.M β) :
    (do let _ ← dataDoneCapture operation probe; next) = (do operation; next) := by
  have h := congrArg (fun action : Leanux.M Unit => do action; next) (dataDoneCapture_erase operation probe)
  simpa only [bind_assoc, pure_bind] using h


def dataDonePrefix (pid : PeerId) (items : List SkbId) : Leanux.M DataDoneObservation := do
  let traversal ← dataDoneCapture (liftWG (timersTraversal pid))
    (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal)
  liftWG (timersAnyAuthenticatedPacketSent pid)
  let (sent, observations) ← liftWG (dataDoneObservedItems pid items false)
  _ ← branch .doneSkbIterate false
  let selected ← branch .doneDataSent sent
  let beforeSent ← Campaign2.Product.read
  let dataHook ← if selected then do
      let cut ← dataDoneCapture (liftWG (timersDataSent pid))
        (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter)
      pure (some cut)
    else pure none
  return ⟨traversal, observations, sent, beforeSent, dataHook⟩


def observedDataDone (pid : PeerId) (items : List SkbId) : Leanux.M DataDoneObservation := do
  let cut ← dataDonePrefix pid items
  liftWG (keepKeyFresh pid)
  return cut


theorem liftWG_bind_variant {α β : Type} (action : WG.M α) (next : α → WG.M β) :
    liftWG (action >>= next) = (liftWG action >>= fun value => liftWG (next value)) := by
  funext entry
  change ((((action.run entry.wg).run entry.ambient) >>= fun ((value, middle), after) =>
    ((next value).run middle).run after) >>= fun ((value, last), ending) =>
      Except.ok (value, {entry with wg := last, ambient := ending})) =
    ((((action.run entry.wg).run entry.ambient) >>= fun ((value, middle), after) =>
      Except.ok (value, {entry with wg := middle, ambient := after})) >>= fun (value, current) =>
        ((next value).run current.wg).run current.ambient >>= fun ((result, last), ending) =>
          Except.ok (result, {current with wg := last, ambient := ending}))
  simp only [bind_assoc]
  cases run : (action.run entry.wg).run entry.ambient with
  | error stop => rfl
  | ok pair => obtain ⟨⟨value, middle⟩, after⟩ := pair; rfl

theorem observedDataDone_erase (pid : PeerId) (items : List SkbId) :
    (do let _ ← observedDataDone pid items; pure ()) = liftWG (createDataDone pid items) := by
  have read_drop {γ : Type} (action : Leanux.M γ) :
      (do let _ ← Campaign2.Product.read; action) = action := rfl
  have unit_drop (action : Leanux.M Unit) : (do action; pure ()) = action := by
    funext entry
    change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
    cases run : action.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨u, final⟩; cases u; rfl
  have lift_pure {γ : Type} (value : γ) : liftWG (pure value) = (pure value : Leanux.M γ) := rfl
  have lift_branch (decision : Decision) (value : Bool) :
      liftWG (branch decision value : WG.M Bool) = (branch decision value : Leanux.M Bool) := rfl
  rw [← dataDoneSource_eq]
  simp only [observedDataDone, dataDonePrefix, dataDoneSource, dataDoneFinish,
    liftWG_bind_variant, lift_branch, bind_assoc,
    Roaming.bind_if, pure_bind, read_drop, unit_drop]
  rw [dataDoneCapture_bind]
  congr 1
  funext ignored
  congr 1
  funext ignored
  rw [← dataDoneObservedItems_erase pid items false]
  simp only [liftWG_bind_variant, lift_pure, bind_assoc, pure_bind]
  congr 1
  funext result
  rcases result with ⟨sent, observations⟩
  congr 1
  funext ignored
  congr 1
  funext selected
  cases selected
  · rfl
  · simp only [ite_true, liftWG_bind_variant]
    change (dataDoneCapture (liftWG (timersDataSent pid))
        (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter)
          >>= fun _ => liftWG (keepKeyFresh pid)) =
      (liftWG (timersDataSent pid) >>= fun _ => liftWG (keepKeyFresh pid))
    exact dataDoneCapture_bind _ _ _


end Leanux.Proofs.WG.TimerDiscipline
