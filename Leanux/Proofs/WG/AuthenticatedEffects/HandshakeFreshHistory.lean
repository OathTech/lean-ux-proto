import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausalReceiver

/-! A callback is attributed to the latest actual consumer admission, with no
intervening admission from another invocation. This strengthens the earlier
existence-only history property while leaving the native receiver unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeCausal

/-- The intervening suffix contains callbacks only. The receipt itself carries
the native MAC and pre-write Noise authentication witnesses. -/
def Available (history : List Event) (pid : PeerId) : Prop :=
  ∃ before receipt after, history = before ++ Event.admission receipt :: after ∧
    after.filterMap admission = [] ∧ receipt.Valid ∧ receipt.ForPeer pid

def Checked (before : List Event) : Event → Prop
  | .admission _ => True
  | .callback _ pid => Available before pid

def Safe (history : List Event) : Prop :=
  ∀ before event after, history = before ++ event :: after → Checked before event

abbrev Inv (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h
abbrev Preserves (body : WGPrefix Event α) := StatePrefixPreserves Inv Safe body

def Ready (pid : PeerId) (h : List Event) (_ : WGWorld) (_ : Ambient) := Safe h ∧ Available h pid

theorem Safe.append {history suffix : List Event} (safe : Safe history)
    (checked : ∀ before event after, suffix = before ++ event :: after → Checked (history ++ before) event) :
    Safe (history ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked history suffix safe checked

theorem Safe.quiet {history suffix : List Event} (safe : Safe history)
    (quiet : suffix.filterMap calls = []) : Safe (history ++ suffix) := by
  apply safe.append
  intro before event after position
  cases event with
  | admission _ => trivial
  | callback kind pid =>
    have member : Event.callback kind pid ∈ suffix := by rw [position]; simp
    have found : () ∈ suffix.filterMap calls := List.mem_filterMap.mpr ⟨_,member,rfl⟩
    simp [quiet] at found

theorem Available.quiet {history suffix : List Event} {pid : PeerId} (available : Available history pid)
    (quiet : suffix.filterMap admission = []) : Available (history ++ suffix) pid := by
  obtain ⟨before,receipt,after,position,noOther,valid,peer⟩ := available
  exact ⟨before,receipt,after ++ suffix,by simp only [position,List.append_assoc,List.cons_append],
    by simp only [List.filterMap_append,noOther,quiet,List.append_nil],valid,peer⟩

theorem Safe.callback {history : List Event} (safe : Safe history)
    (kind : Kind) (pid : PeerId) (available : Available history pid) :
    Safe (history ++ [.callback kind pid]) := by
  apply safe.append
  intro before event after position
  cases before with
  | nil => cases position; simpa only [Checked,List.append_nil] using available
  | cons first rest =>
    have lengths := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

theorem lift_ready (pid : PeerId) (action : WG.M α) :
    StatePrefixPreserves (Ready pid) Safe (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi => hi.1) (fun _ _ _ _ _ _ hi _ => hi)

theorem call_ready (kind : Kind) (pid : PeerId) (action : WG.M α) :
    StatePrefixPreserves (Ready pid) Safe (call kind pid action) := by
  unfold call
  refine StatePrefixEnsures.bind
    (StatePrefixEnsures.emit (P := Ready pid) (S := Safe) (Q := fun _ => Ready pid) (.callback kind pid) ?_ ?_) ?_
  · intro h w a hi; exact hi.1.callback kind pid hi.2
  · intro h w a hi
    exact ⟨hi.1.callback kind pid hi.2,hi.2.quiet rfl⟩
  · intro doneUnit; exact lift_ready pid action

theorem empty_safe : Safe [] := by
  intro before event after position
  have lengths := congrArg List.length position
  simp at lengths

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
