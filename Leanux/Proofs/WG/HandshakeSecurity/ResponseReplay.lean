import Leanux.Proofs.WG.HandshakeSecurity.H1Contracts
import Leanux.Proofs.Logged.NativeCapture

/-! Actual response-consumer journals. H1 supplies its already-proved source
edges; the invariant derives the no-repeat security consequence over any
sequence of original calls, including completed calls before a later Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResponseReplay
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Receipt where
  message : List UInt8
  execution : WGRunWitness (Option PeerId)

def Receipt.Valid (r : Receipt) : Prop := r.execution.Valid (consumeResponse r.message)

def observed (msg : List UInt8) : WGPrefix Receipt (Option PeerId) :=
  receiptWGObserved (liftWGPrefix (consumeResponse msg)) (fun r => ⟨msg, r⟩)

def successes (h : List Receipt) : List PeerId := h.filterMap (·.execution.value)

def Safe (h : List Receipt) : Prop :=
  (∀ r ∈ h, r.Valid) ∧ (successes h).Nodup

def Inv (h : List Receipt) (w : WGWorld) : Prop :=
  Safe h ∧ ∀ pid ∈ successes h, handshakeTagAt w pid ≠ some HANDSHAKE_CREATED_INITIATION

theorem initial (w : WGWorld) : Inv [] w := ⟨⟨by simp, by simp [successes]⟩, by simp [successes]⟩

theorem erases (msg : List UInt8) : ErasesStatePrefix (observed msg) (consumeResponse msg) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem append_valid (H1 : H1ResponseEdges) (h : List Receipt) (r : Receipt)
    (hi : Inv h r.execution.before) (valid : r.Valid) : Inv (h ++ [r]) r.execution.after := by
  obtain ⟨entry, tags⟩ := H1 r.message r.execution.before r.execution.after
    r.execution.ambientBefore r.execution.ambientAfter r.execution.value valid
  have receipts : ∀ e ∈ h ++ [r], e.Valid := by
    intro e member
    rcases List.mem_append.mp member with old | current
    · exact hi.1.1 e old
    · have equal := List.mem_singleton.mp current
      simpa only [equal] using valid
  cases hr : r.execution.value with
  | none =>
    have same : successes (h ++ [r]) = successes h := by simp [successes, List.filterMap_append, hr]
    refine ⟨⟨receipts, same ▸ hi.1.2⟩, ?_⟩
    intro pid member
    rw [tags pid]
    simpa [hr] using hi.2 pid (same ▸ member)
  | some pid =>
    have unused : pid ∉ successes h := by
      intro member
      exact hi.2 pid member (entry pid hr)
    have appended : successes (h ++ [r]) = successes h ++ [pid] := by
      simp [successes, List.filterMap_append, hr]
    refine ⟨⟨receipts, ?_⟩, ?_⟩
    · rw [appended]
      apply List.nodup_append.mpr
      refine ⟨hi.1.2, by simp, ?_⟩
      intro target member current currentMember equal
      have same := List.mem_singleton.mp currentMember
      exact unused ((equal.trans same) ▸ member)
    · intro target member
      rw [tags target]
      by_cases same : target = pid
      · simp [hr, same, HANDSHAKE_CONSUMED_RESPONSE, HANDSHAKE_CREATED_INITIATION]
      · have prior : target ∈ successes h := by simpa [appended, same] using member
        simpa [hr, Ne.symm same] using hi.2 target prior

theorem preserves (H1 : H1ResponseEdges) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => Inv h w) Safe (observed msg) := by
  intro w a h hi
  have equation := runWGPrefix_receiptWGObserved
    (liftWGPrefix (consumeResponse msg)) (fun r => (⟨msg, r⟩ : Receipt)) w a h
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (observed msg) w a h = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : ((consumeResponse msg).run w).run a with
  | error stop => exact ⟨[], by simp, hi.1, trivial⟩
  | ok out =>
    rcases out with ⟨⟨result, v⟩, b⟩
    have post := append_valid H1 h ⟨msg, ⟨result, w, v, a, b⟩⟩ hi run
    exact ⟨_, rfl, post.1, post⟩

def sequence : List (List UInt8) → WGPrefix Receipt Unit
  | [] => pure ()
  | msg :: rest => do
    _ ← observed msg
    sequence rest

def original : List (List UInt8) → WG.M Unit
  | [] => pure ()
  | msg :: rest => do
    _ ← consumeResponse msg
    original rest

theorem sequence_erases (messages : List (List UInt8)) :
    ErasesStatePrefix (sequence messages) (original messages) := by
  induction messages with
  | nil => exact erasesStatePrefix_pure ()
  | cons msg rest ih => exact erasesStatePrefix_bind (erases msg) (fun _ => ih)

theorem sequence_preserves (H1 : H1ResponseEdges) (messages : List (List UInt8)) :
    StatePrefixPreserves (fun h w _ => Inv h w) Safe (sequence messages) := by
  induction messages with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | cons msg rest ih => exact StatePrefixEnsures.bind (preserves H1 msg) (fun _ => ih)

/-- Session completion cannot refresh the initiation state consumed by a
response, so a real installation may be interleaved without enabling replay. -/
theorem session_preserves (H1 : H1SessionEffects) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv h w) Safe
      (liftWGPrefix (beginSession pid) : WGPrefix Receipt Bool) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a result v b hi run
  have tags := (H1 pid w v a b result run).2.1
  refine ⟨hi.1, ?_⟩
  intro target member
  rw [tags target]
  split
  · simp [HANDSHAKE_ZEROED, HANDSHAKE_CREATED_INITIATION]
  · exact hi.2 target member

inductive Action where
  | response (msg : List UInt8)
  | session (pid : PeerId)

def actionObserved : Action → WGPrefix Receipt Unit
  | .response msg => do _ ← observed msg; pure ()
  | .session pid => do _ ← liftWGPrefix (beginSession pid); pure ()

def actionOriginal : Action → WG.M Unit
  | .response msg => do _ ← consumeResponse msg; pure ()
  | .session pid => do _ ← beginSession pid; pure ()

def mixedSequence : List Action → WGPrefix Receipt Unit
  | [] => pure ()
  | action :: rest => actionObserved action *> mixedSequence rest

def mixedOriginal : List Action → WG.M Unit
  | [] => pure ()
  | action :: rest => actionOriginal action *> mixedOriginal rest

theorem action_erases (action : Action) :
    ErasesStatePrefix (actionObserved action) (actionOriginal action) := by
  cases action with
  | response msg => exact erasesStatePrefix_bind (erases msg) (fun _ => erasesStatePrefix_pure ())
  | session pid => exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure ())

theorem action_preserves (responseH1 : H1ResponseEdges) (sessionH1 : H1SessionEffects)
    (action : Action) : StatePrefixPreserves (fun h w _ => Inv h w) Safe (actionObserved action) := by
  have done := StatePrefixEnsures.pure (E := Receipt) (Outer := WGWorld) (Inner := Ambient)
    (P := fun h w _ => Inv h w) (S := Safe) (Q := fun _ h w _ => Inv h w)
    () (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  cases action with
  | response msg => exact StatePrefixEnsures.bind (preserves responseH1 msg) (fun _ => done)
  | session pid => exact StatePrefixEnsures.bind (session_preserves sessionH1 pid) (fun _ => done)

theorem mixed_erases (actions : List Action) :
    ErasesStatePrefix (mixedSequence actions) (mixedOriginal actions) := by
  induction actions with
  | nil => exact erasesStatePrefix_pure ()
  | cons action rest ih => exact erasesStatePrefix_bind (action_erases action) (fun _ => ih)

theorem mixed_preserves (responseH1 : H1ResponseEdges) (sessionH1 : H1SessionEffects)
    (actions : List Action) : StatePrefixPreserves (fun h w _ => Inv h w) Safe (mixedSequence actions) := by
  induction actions with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | cons action rest ih =>
    exact StatePrefixEnsures.bind (action_preserves responseH1 sessionH1 action) (fun _ => ih)

end Leanux.Proofs.WG.HandshakeSecurity.ResponseReplay
