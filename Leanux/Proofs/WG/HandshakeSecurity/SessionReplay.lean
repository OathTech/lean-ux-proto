import Leanux.Proofs.WG.HandshakeSecurity.H1Contracts
import Leanux.Proofs.Logged.NativeCapture

/-! Completed native session calls consume their response state once. H1's
named effects stay visible; this sequence contains no handshake recreation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SessionReplay
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Receipt where
  peer : PeerId
  execution : WGRunWitness Bool

def Receipt.Valid (r : Receipt) : Prop := r.execution.Valid (beginSession r.peer)

def Receipt.Counted (r : Receipt) : Prop :=
  r.execution.after.keypairCounter = r.execution.before.keypairCounter +
    (if r.execution.value then 1 else 0)

def observed (pid : PeerId) : WGPrefix Receipt Bool :=
  receiptWGObserved (liftWGPrefix (beginSession pid)) (fun r => ⟨pid, r⟩)

def successes (h : List Receipt) : List PeerId :=
  h.filterMap fun r => if r.execution.value then some r.peer else none

def Safe (h : List Receipt) : Prop :=
  (∀ r ∈ h, r.Valid ∧ r.Counted) ∧ (successes h).Nodup

def Inv (initialCounter : Nat) (h : List Receipt) (w : WGWorld) : Prop :=
  Safe h ∧ (∀ pid ∈ successes h, handshakeTagAt w pid = some HANDSHAKE_ZEROED) ∧
    w.keypairCounter = initialCounter + (successes h).length

theorem initial (w : WGWorld) : Inv w.keypairCounter [] w := by
  exact ⟨⟨by simp, by simp [successes]⟩, by simp [successes], by simp [successes]⟩

theorem erases (pid : PeerId) : ErasesStatePrefix (observed pid) (beginSession pid) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem append_valid (H1 : H1SessionEffects) (counter : Nat) (h : List Receipt) (r : Receipt)
    (hi : Inv counter h r.execution.before) (valid : r.Valid) :
    Inv counter (h ++ [r]) r.execution.after := by
  obtain ⟨entry, tags, count⟩ := H1 r.peer r.execution.before r.execution.after
    r.execution.ambientBefore r.execution.ambientAfter r.execution.value valid
  have receipts : ∀ e ∈ h ++ [r], e.Valid ∧ e.Counted := by
    intro e member
    rcases List.mem_append.mp member with old | current
    · exact hi.1.1 e old
    · have equal := List.mem_singleton.mp current
      subst e
      exact ⟨valid, count⟩
  cases hr : r.execution.value with
  | false =>
    have same : successes (h ++ [r]) = successes h := by simp [successes, List.filterMap_append, hr]
    refine ⟨⟨receipts, same ▸ hi.1.2⟩, ?_, ?_⟩
    · intro pid member
      rw [tags pid]
      simpa [hr] using hi.2.1 pid (same ▸ member)
    · simpa [same, hr, hi.2.2] using count
  | true =>
    have unused : r.peer ∉ successes h := by
      intro member
      have before := entry hr
      rw [hi.2.1 r.peer member] at before
      simp [HANDSHAKE_ZEROED, HANDSHAKE_CREATED_RESPONSE, HANDSHAKE_CONSUMED_RESPONSE] at before
    have appended : successes (h ++ [r]) = successes h ++ [r.peer] := by
      simp [successes, List.filterMap_append, hr]
    refine ⟨⟨receipts, ?_⟩, ?_, ?_⟩
    · rw [appended]
      apply List.nodup_append.mpr
      refine ⟨hi.1.2, by simp, ?_⟩
      intro target member current currentMember equal
      have same := List.mem_singleton.mp currentMember
      exact unused ((equal.trans same) ▸ member)
    · intro target member
      rw [tags target]
      by_cases same : target = r.peer
      · simp [hr, same]
      · have prior : target ∈ successes h := by simpa [appended, same] using member
        simpa [hr, same] using hi.2.1 target prior
    · simp only [hr, ite_true, hi.2.2] at count
      simpa [appended, Nat.add_assoc] using count

theorem preserves (H1 : H1SessionEffects) (counter : Nat) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Inv counter h w) Safe (observed pid) := by
  intro w a h hi
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (beginSession pid))
    (fun r => (⟨pid, r⟩ : Receipt)) w a h
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (observed pid) w a h = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : ((beginSession pid).run w).run a with
  | error stop => exact ⟨[], by simp, hi.1, trivial⟩
  | ok out =>
    rcases out with ⟨⟨result, v⟩, b⟩
    have post := append_valid H1 counter h ⟨pid, ⟨result, w, v, a, b⟩⟩ hi run
    exact ⟨_, rfl, post.1, post⟩

def sequence : List PeerId → WGPrefix Receipt Unit
  | [] => pure ()
  | pid :: rest => do
    _ ← observed pid
    sequence rest

def original : List PeerId → WG.M Unit
  | [] => pure ()
  | pid :: rest => do
    _ ← beginSession pid
    original rest

theorem sequence_erases (peers : List PeerId) :
    ErasesStatePrefix (sequence peers) (original peers) := by
  induction peers with
  | nil => exact erasesStatePrefix_pure ()
  | cons pid rest ih => exact erasesStatePrefix_bind (erases pid) (fun _ => ih)

theorem sequence_preserves (H1 : H1SessionEffects) (counter : Nat) (peers : List PeerId) :
    StatePrefixPreserves (fun h w _ => Inv counter h w) Safe (sequence peers) := by
  induction peers with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)
  | cons pid rest ih => exact StatePrefixEnsures.bind (preserves H1 counter pid) (fun _ => ih)

end Leanux.Proofs.WG.HandshakeSecurity.SessionReplay
