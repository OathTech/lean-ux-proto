import Leanux.Proofs.Logged.Projected
import Leanux.Proofs.Logged.Capture
import Leanux.Env.Batch

set_option maxHeartbeats 1000000

/-! The actual stack callback visits its supplied GRO entries in order.
Occurrence numbers label entries independently of payloads and skb values. Their
distinctness and connection to a poll's removals is a separate caller obligation. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

structure GroEntry where
  occurrence : Nat
  skb : SkbId
  bytes : List UInt8

inductive GroEvent where
  | removed (occurrence : Nat) (skb : SkbId)
  | buffered (entry : GroEntry)
  | entered (entry : GroEntry)

def enterGro (e : GroEntry) : PrefixM GroEvent Unit := do
  emitPrefix (.entered e)
  liftPrefix (Leanux.Env.deliverInner e.bytes)

def flushGro (entries : List GroEntry) : PrefixM GroEvent Unit := entries.forM enterGro

theorem flushGro_erases (entries : List GroEntry) :
    ErasesPrefix (flushGro entries) ((entries.map GroEntry.bytes).forM Leanux.Env.deliverInner) := by
  induction entries with
  | nil => exact erasesPrefix_pure _
  | cons e rest ih =>
    simp only [flushGro, List.forM_eq_forM, List.forM_cons, List.map_cons] at *
    exact erasesPrefix_bind (emitThen_erases _ _) (fun _ => ih)

/-- A failed stack callback retains its entered occurrence, but never emits
entries for the unvisited suffix. Normal completion visits every entry. -/
theorem flushGro_prefix (entries : List GroEntry) (w : World) (h : List GroEvent) :
    ∃ visited remaining, entries = visited ++ remaining ∧
      (runPrefix (flushGro entries) w h).2 = h ++ visited.map GroEvent.entered ∧
      (∀ x v, (runPrefix (flushGro entries) w h).1 = .ok (x, v) → remaining = []) := by
  induction entries generalizing w h with
  | nil => exact ⟨[], [], rfl, by simp [flushGro, List.forM_eq_forM], fun _ _ _ => rfl⟩
  | cons e rest ih =>
    have he : runPrefix (flushGro (e :: rest)) w h =
        match (Leanux.Env.deliverInner e.bytes).run w with
        | .error stop => (.error stop, h ++ [.entered e])
        | .ok (_, v) => runPrefix (flushGro rest) v (h ++ [.entered e]) := by
      simp only [flushGro, List.forM_eq_forM, List.forM_cons, enterGro,
        runPrefix_bind, runPrefix_emit, runPrefix_lift]
      cases (Leanux.Env.deliverInner e.bytes).run w <;> rfl
    rw [he]
    cases hr : (Leanux.Env.deliverInner e.bytes).run w with
    | error stop => exact ⟨[e], rest, rfl, rfl, by simp⟩
    | ok out =>
      rcases out with ⟨u, v⟩
      obtain ⟨visited, remaining, hv, hh, ho⟩ := ih v (h ++ [.entered e])
      exact ⟨e :: visited, remaining, by simp [hv],
        by simpa [List.map_cons, List.append_assoc] using hh, ho⟩

end Leanux.Proofs.WG.Queues
