import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryPath
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEncryptionFocus

/-! Fixed pieces of the original encryption callback. The loop stops at the
first failed encryption result, but publication still receives the original
whole batch. No callback or source guard is replaced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal

abbrev ops : EncryptionSource.Ops CausalJournal.Event :=
  EncryptionSource.observed (CausalJournal.Event.old ∘ Journal.Event.encrypted)
    (fun event => (CausalJournal.old? event).bind Journal.encryption?)
    CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal?

def iteration (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (state : PacketState) : PrefixM CausalJournal.Event (ForInStep PacketState) := do
  _ ← ops.step (branch .encWorkerSkbIterate true)
  let encrypted ← ops.packet headId head id
  if ← ops.step (branch .encWorkerEncrypted encrypted.isSome) then
    ops.step (liftWG (setTxSkb id fun p => {p with bytes := encrypted.getD []}))
    pure (.yield state)
  else pure (.done .dead)

def loop (headId : SkbId) (head : RunWitness DataPacket) (items : List SkbId)
    (state : PacketState) : PrefixM CausalJournal.Event PacketState :=
  forIn items state (fun id state => iteration headId head id state)

def guard (state : PacketState) : PrefixM CausalJournal.Event Unit := do
  if state == .crypted then _ ← ops.step (branch .encWorkerSkbIterate false)

def publish (items : List SkbId) (state : PacketState) : PrefixM CausalJournal.Event Bool := do
  ops.publish items state
  pure true

def afterLoop (items : List SkbId) (state : PacketState) : PrefixM CausalJournal.Event Bool := do
  guard state
  publish items state

def publicationPrefix (headId : SkbId) (head : RunWitness DataPacket) (items : List SkbId) :
    PrefixM CausalJournal.Event PacketState := do
  let state ← loop headId head items .crypted
  guard state
  pure state

theorem loop_nil (headId : SkbId) (head : RunWitness DataPacket) (state : PacketState) :
    loop headId head [] state = pure state := rfl

theorem loop_cons (headId : SkbId) (head : RunWitness DataPacket) (id : SkbId)
    (rest : List SkbId) (state : PacketState) :
    loop headId head (id :: rest) state = (do
      match ← iteration headId head id state with
      | .done next => pure next
      | .yield next => loop headId head rest next) := by
  unfold loop
  rw [List.forIn_cons]
  apply congrArg (fun next : ForInStep PacketState → PrefixM CausalJournal.Event PacketState =>
    iteration headId head id state >>= next)
  funext next
  cases next <;> rfl

theorem afterHead_factor (items : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    EncryptionSource.afterHead ops items headId head =
      (loop headId head items .crypted >>= afterLoop items) := by
  change (loop headId head items .crypted >>= fun state =>
    if state == .crypted then do
      _ ← ops.step (branch .encWorkerSkbIterate false)
      ops.publish items state
      pure true
    else do ops.publish items state; pure true) = _
  apply congrArg (fun next : PacketState → PrefixM CausalJournal.Event Bool =>
    loop headId head items .crypted >>= next)
  funext state
  unfold afterLoop guard publish
  split <;> simp only [bind_assoc,pure_bind]

theorem publication_factor (items : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    EncryptionSource.afterHead ops items headId head =
      (publicationPrefix headId head items >>= publish items) := by
  rw [afterHead_factor]
  simp only [publicationPrefix,bind_assoc,pure_bind]
  rfl

def headPrefix (items : List SkbId) : PrefixM CausalJournal.Event (SkbId × RunWitness DataPacket) := do
  _ ← ops.step (branch .encWorkerConsumed true)
  let some headId := items.head? | ops.step (invariant "an empty ring item")
  let head ← ops.head headId
  pure (headId,head)

theorem tail_factor (items : List SkbId) (headId : SkbId) (selected : items.head? = some headId) :
    EncryptionSource.tail ops (some items) =
      (headPrefix items >>= fun (headId,head) => EncryptionSource.afterHead ops items headId head) := by
  simp only [EncryptionSource.tail,headPrefix,Option.isSome_some,selected,bind_assoc,pure_bind]

theorem encrypt_run (item : Option (List SkbId)) (w : World) (history : List CausalJournal.Event) :
    runPrefix (CausalJournal.encrypt item) w history =
      match runPrefix (EncryptionSource.tail ops item) w history with
      | (.error reason,last) => (.error reason,last)
      | (.ok (value,v),last) =>
        (.ok (value,v),last ++ [.old (.encryptionReturn item ⟨value,w,v⟩)]) :=
  by
    change runPrefix (receiptObserved (EncryptionSource.tail ops item)
      (fun run => .old (.encryptionReturn item run))) w history = _
    rw [runPrefix_receiptObserved]
    cases runPrefix (EncryptionSource.tail ops item) w history with
    | mk result last => cases result <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
