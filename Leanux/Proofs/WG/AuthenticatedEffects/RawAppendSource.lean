import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketCut

/-! A direct observer at the original final socket append. This source does
not consume completed socket receipts. The original fallible socket prefix
precedes the append, and the event is emitted immediately after that append.
Repeated equal datagrams remain distinct list positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Event where
  before : List SentDatagram
  datagram : SentDatagram

/-- Decode only a single actual append; malformed deltas are not accepted. -/
def ofSent (before after : List SentDatagram) : Option Event :=
  match after.drop before.length with
  | [datagram] => some ⟨before,datagram⟩
  | _ => none

theorem ofSent_same (sent : List SentDatagram) : ofSent sent sent = none := by
  simp [ofSent]

theorem ofSent_append (sent : List SentDatagram) (datagram : SentDatagram) :
    ofSent sent (sent ++ [datagram]) = some ⟨sent,datagram⟩ := by
  simp [ofSent]

def append (datagram : SentDatagram) : WGPrefix Event Int := do
  let before ← liftWGPrefix (get : WG.M WGWorld)
  liftWGPrefix (modify fun w => {w with sent := w.sent ++ [datagram]})
  emitStatePrefix ⟨before.sent,datagram⟩
  pure 0

def socket (args : ProtocolSocket.Args) : WGPrefix Event Int := do
  match ← liftWGPrefix args.beforeAppend with
  | .error err => pure err
  | .ok datagram => append datagram

theorem append_run (datagram : SentDatagram) (w : WGWorld) (a : Ambient) (history : List Event) :
    runWGPrefix (append datagram) w a history =
      (.ok ((0,{w with sent := w.sent ++ [datagram]}),a),history ++ [⟨w.sent,datagram⟩]) := rfl

theorem socket_run (args : ProtocolSocket.Args) (w : WGWorld) (a : Ambient) (history : List Event) :
    runWGPrefix (socket args) w a history =
      match (args.beforeAppend.run w).run a with
      | .error stop => (.error stop,history)
      | .ok ((.error err,u),b) => (.ok ((err,u),b),history)
      | .ok ((.ok datagram,u),b) =>
          (.ok ((0,{u with sent := u.sent ++ [datagram]}),b),history ++ [⟨u.sent,datagram⟩]) := by
  unfold socket
  rw [liftWG_bind_run]
  cases run : (args.beforeAppend.run w).run a with
  | error stop => rfl
  | ok result =>
    obtain ⟨⟨result,u⟩,b⟩ := result
    cases result <;> rfl

theorem socket_erases (args : ProtocolSocket.Args) : ErasesStatePrefix (socket args) args.action := by
  intro w a history
  change (runWGPrefix (socket args) w a history).1 = (args.action.run w).run a
  rw [socket_run,ProtocolSocket.append_factor,native_bind_run]
  cases run : (args.beforeAppend.run w).run a with
  | error stop => rfl
  | ok result =>
    obtain ⟨⟨result,u⟩,b⟩ := result
    cases result <;> rfl

theorem socket_appends (args : ProtocolSocket.Args) : StateAppends (socket args) := by
  intro w a history
  change ∃ suffix, (runWGPrefix (socket args) w a history).2 = history ++ suffix
  rw [socket_run]
  cases run : (args.beforeAppend.run w).run a with
  | error stop => exact ⟨[],by simp⟩
  | ok result =>
    obtain ⟨⟨result,u⟩,b⟩ := result
    cases result with
    | error err => exact ⟨[],by simp⟩
    | ok datagram => exact ⟨[⟨u.sent,datagram⟩],rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
