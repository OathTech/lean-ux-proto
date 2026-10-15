import Leanux.Proofs.WG.TimerDiscipline.DataDoneModel
import Leanux.Proofs.WG.TimerDiscipline.ObservationClaims
import Leanux.Proofs.WG.Roaming.PollEndpointSource
import Leanux.WG.Data

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do Campaign2
variable {α β : Type}

def dataDoneStep (pid : PeerId) (id : SkbId) (dataSent : Bool) : M (ForInStep Bool) := do
  let skb ← getTxSkb id
  _ ← branch .doneSkbIterate true
  let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← sendSkbToPeer pid skb.bytes skb.ds
  let qualifies ← WG.andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive)
  if qualifies then return .yield true
  return .yield dataSent


def dataDoneFinish (pid : PeerId) (dataSent : Bool) : M Unit := do
  _ ← branch .doneSkbIterate false
  if ← branch .doneDataSent dataSent then timersDataSent pid
  keepKeyFresh pid


def dataDoneSource (pid : PeerId) (item : List SkbId) : M Unit := do
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let dataSent ← forIn item false (dataDoneStep pid)
  dataDoneFinish pid dataSent


theorem dataDoneSource_eq (pid : PeerId) (item : List SkbId) :
    dataDoneSource pid item = createDataDone pid item := by
  rfl


def dataDoneObservedStep (pid : PeerId) (id : SkbId) (dataSent : Bool) :
    M (ForInStep Bool × DataDoneItem) := do
  let skb ← getTxSkb id
  _ ← branch .doneSkbIterate true
  let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
  let sent ← sendSkbToPeer pid skb.bytes skb.ds
  let qualifies ← WG.andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive)
  if qualifies then return (.yield true, ⟨id, skb, sent, qualifies⟩)
  return (.yield dataSent, ⟨id, skb, sent, qualifies⟩)


theorem dataDoneObservedStep_erase (pid : PeerId) (id : SkbId) (before : Bool) :
    (do let result ← dataDoneObservedStep pid id before; pure result.1) = dataDoneStep pid id before := by
  simp only [dataDoneObservedStep, dataDoneStep, bind_assoc, pure_bind]
  congr 1
  funext packet
  congr 1
  funext ignored
  congr 1
  funext sent
  congr 1
  funext qualifies
  cases qualifies <;> rfl


def dataDoneObservedItems (pid : PeerId) : List SkbId → Bool → M (Bool × List DataDoneItem)
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


def dataDoneCapture (operation : M Unit) (probe : M α) : M (DataDoneTimerCut α) := do
  let before ← Campaign2.read
  let value ← observed operation probe
  let after ← Campaign2.read
  return ⟨before, value.1, after⟩


theorem dataDoneCapture_erase (operation : M Unit) (probe : M α) :
    (do let _ ← dataDoneCapture operation probe; pure ()) = operation := by
  calc
    _ = (do let value ← observed operation probe; pure value.2) := by
      funext entry
      change (((observed operation probe).run entry >>= fun out =>
        Except.ok (DataDoneTimerCut.mk (snapshot entry) out.1.1 (snapshot out.2), out.2))
          >>= fun out => Except.ok ((), out.2)) =
        ((observed operation probe).run entry >>= fun out => Except.ok (out.1.2, out.2))
      cases run : (observed operation probe).run entry with
      | error err => rfl
      | ok pair => rcases pair with ⟨⟨value, unit⟩, final⟩; cases unit; rfl
    _ = operation := observed_erase operation probe


theorem dataDoneCapture_bind (operation : M Unit) (probe : M α) (next : M β) :
    (do let _ ← dataDoneCapture operation probe; next) = (do operation; next) := by
  have h := congrArg (fun action : M Unit => do action; next) (dataDoneCapture_erase operation probe)
  simpa only [bind_assoc, pure_bind] using h


def dataDonePrefix (pid : PeerId) (items : List SkbId) : M DataDoneObservation := do
  let traversal ← dataDoneCapture (timersTraversal pid)
    (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal)
  timersAnyAuthenticatedPacketSent pid
  let (sent, observations) ← dataDoneObservedItems pid items false
  _ ← branch .doneSkbIterate false
  let selected ← branch .doneDataSent sent
  let beforeSent ← Campaign2.read
  let dataHook ← if selected then do
      let cut ← dataDoneCapture (timersDataSent pid)
        (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter)
      pure (some cut)
    else pure none
  return ⟨traversal, observations, sent, beforeSent, dataHook⟩


def observedDataDone (pid : PeerId) (items : List SkbId) : M DataDoneObservation := do
  let cut ← dataDonePrefix pid items
  keepKeyFresh pid
  return cut


theorem observedDataDone_erase (pid : PeerId) (items : List SkbId) :
    (do let _ ← observedDataDone pid items; pure ()) = createDataDone pid items := by
  have read_drop {γ : Type} (action : M γ) : (do let _ ← Campaign2.read; action) = action := rfl
  have unit_drop (action : M Unit) : (do action; pure ()) = action := by
    funext entry
    change (action.run entry >>= fun out => Except.ok ((), out.2)) = action.run entry
    cases run : action.run entry with
    | error err => rfl
    | ok pair => rcases pair with ⟨unit, final⟩; cases unit; rfl
  rw [← dataDoneSource_eq]
  simp only [observedDataDone, dataDonePrefix, dataDoneSource, dataDoneFinish, bind_assoc,
    Roaming.bind_if, pure_bind, read_drop, unit_drop]
  rw [dataDoneCapture_bind]
  congr 1
  funext ignored
  congr 1
  funext ignored
  rw [← dataDoneObservedItems_erase pid items false]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext result
  rcases result with ⟨sent, observations⟩
  congr 1
  funext ignored
  congr 1
  funext selected
  cases selected
  · rfl
  · change (dataDoneCapture (timersDataSent pid)
        (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter)
          >>= fun _ => keepKeyFresh pid) =
      (timersDataSent pid >>= fun _ => keepKeyFresh pid)
    exact dataDoneCapture_bind _ _ _


end Leanux.Proofs.WG.TimerDiscipline
