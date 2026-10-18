import Leanux.Proofs.WG.AuthenticatedEffects.SocketObservation

/-! Native cookie-reply egress receipts, preserved even when a later native
continuation stops. These are actual append receipts rather than attempts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

def replySocketEmitted (target : ReplyTarget) (bytes : List UInt8) :
    WGPrefix DatagramReceipt Unit := do
  if target.ipv4 then
    _ ← send4Emitted target.endpoint bytes 0
    pure ()
  else
    _ ← send6Emitted target.endpoint bytes 0
    pure ()

theorem replySocketEmitted_erases (target : ReplyTarget) (bytes : List UInt8) :
    ErasesStatePrefix (replySocketEmitted target bytes) (replySocket target bytes) := by
  unfold replySocketEmitted replySocket
  simp only [discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  split
  · exact erasesStatePrefix_bind (send4Emitted_erases _ _ _) (fun _ => erasesStatePrefix_pure ())
  · exact erasesStatePrefix_bind (send6Emitted_erases _ _ _) (fun _ => erasesStatePrefix_pure ())

theorem replySocketEmitted_receipts (target : ReplyTarget) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (replySocketEmitted target bytes) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint = target.endpoint ∧ r.bytes = bytes ∧ r.ds = 0 := by
  unfold replySocketEmitted
  split <;> rw [bind_pure_history] <;> exact socketEmitted_receipts _ _ _ _ _ _ _

def replyEmitted (src : SkbSource) (bytes : List UInt8) : WGPrefix DatagramReceipt Unit := do
  match ← liftWGPrefix (replyFront src) with
  | none => pure ()
  | some target => replySocketEmitted target bytes

theorem replyEmitted_erases (src : SkbSource) (bytes : List UInt8) :
    ErasesStatePrefix (replyEmitted src bytes) (sendBufferAsReplyToSkb src bytes) := by
  rw [reply_factor]
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro target
  cases target with
  | none => exact erasesStatePrefix_pure ()
  | some t => exact replySocketEmitted_erases t bytes

theorem replyEmitted_receipts (src : SkbSource) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (h : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (replyEmitted src bytes) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint.addr = src.saddr ∧ r.endpoint.port = src.sport ∧
        r.bytes = bytes ∧ r.ds = 0 := by
  unfold replyEmitted
  rw [liftWG_bind_run]
  cases front : ((replyFront src).run w).run a with
  | error err => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨⟨target,u⟩,b⟩
    cases target with
    | none => exact ⟨[],by simp [runWGPrefix]⟩
    | some t =>
      have source := replyFront_source src w u a b t front
      obtain ⟨suffix,eq,len,members⟩ := replySocketEmitted_receipts t bytes u b h
      refine ⟨suffix,eq,len,?_⟩
      intro r mem
      obtain ⟨valid,endpoint,data,ds⟩ := members r mem
      exact ⟨valid,by simpa only [endpoint] using source.1,
        by simpa only [endpoint] using source.2,data,ds⟩

end Leanux.Proofs.WG.AuthenticatedEffects
