import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketReceipts

/-! The complete native socket factors at its final datagram append. Loopback,
routing, accounting and socket-port checks all precede this cut; no fallible
continuation lies between the append and the protocol receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def Args.route (args : Args) : WG.M (Except Int Route) :=
  if args.ipv4 then socket4Front args.endpoint args.cache args.bytes args.ds args.exactRx
  else socket6Front args.endpoint args.cache

def Args.beforeAppend (args : Args) : WG.M (Except Int SentDatagram) := do
  match ← args.route with
  | .error err => pure (.error err)
  | .ok route =>
    let port ← TransmitSecurity.Completion.tunnelFront args.endpoint args.bytes route args.exactRx
    pure (.ok (tunnelDatagram args.endpoint args.bytes args.ds route port))

def appendResult : Except Int SentDatagram → WG.M Int
  | .error err => pure err
  | .ok datagram => do
    modify fun w => {w with sent := w.sent ++ [datagram]}
    pure 0

theorem append_factor (args : Args) : args.action = (args.beforeAppend >>= appendResult) := by
  have native : args.action = (args.route >>= socketResult args.endpoint args.bytes args.ds args.exactRx) := by
    unfold Args.action Args.route
    cases args.ipv4
    · exact TransmitSecurity.Completion.socket6_factor _ _ _ _ _
    · rw [←send4Source_eq,TransmitSecurity.Completion.socket4Front_factor]
      rfl
  rw [native]
  unfold Args.beforeAppend
  simp only [bind_assoc]
  apply congrArg (fun continuation => args.route >>= continuation)
  funext route
  cases route with
  | error err => simp only [socketResult,pure_bind,appendResult]
  | ok route =>
    simp only [socketResult,TransmitSecurity.Completion.tunnel_factor,bind_assoc,pure_bind,appendResult]

theorem beforeAppend_sent (args : Args) : SameView WGWorld.sent args.beforeAppend := by
  intro initial
  change Preserves (fun (w : WGWorld) => w.sent = initial) _
  unfold Args.beforeAppend
  apply preserves_bind
  · unfold Args.route
    split
    · exact (TransmitSecurity.Completion.socket4Front_sent _ _ _ _ _).wp (fun sent => sent = initial)
    · exact (TransmitSecurity.Completion.socket6Front_sent _ _).wp (fun sent => sent = initial)
  · intro route
    cases route with
    | error err => exact preserves_pure _
    | ok route =>
      exact preserves_bind
        ((TransmitSecurity.Completion.tunnelFront_sent _ _ _ _).wp (fun sent => sent = initial))
        (fun _ => preserves_pure _)

/-- If the native socket stops, its final append has not been reached. This
is a source-cut implication, not an inference from completed receipts. -/
theorem stops_before_append (args : Args) (w : WGWorld) (a : Ambient) (stop : Stop)
    (stopped : (args.action.run w).run a = .error stop) :
    (args.beforeAppend.run w).run a = .error stop := by
  rw [append_factor,native_bind_run] at stopped
  cases front : (args.beforeAppend.run w).run a with
  | error err => simpa only [front,Except.error.injEq] using stopped
  | ok out =>
    rcases out with ⟨⟨result,u⟩,b⟩
    rw [front] at stopped
    cases result <;> cases stopped

theorem append_receipt (record : Receipt Context → E) (context : Context) (args : Args)
    (w u : WGWorld) (a b : Ambient) (history : List E) (datagram : SentDatagram)
    (front : (args.beforeAppend.run w).run a = .ok ((.ok datagram,u),b)) :
    runWGPrefix (socket record context args) w a history =
      (.ok ((0,{u with sent := u.sent ++ [datagram]}),b),
        history ++ [record ⟨context,args,⟨0,w,{u with sent := u.sent ++ [datagram]},a,b⟩⟩]) := by
  have native : (args.action.run w).run a = .ok ((0,{u with sent := u.sent ++ [datagram]}),b) := by
    rw [append_factor,native_bind_run,front]
    rfl
  unfold socket
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,native]

/-- An actual append's receipt precedes every later retained continuation
event, even when that continuation internally Stops. -/
theorem append_receipt_retained (record : Receipt Context → E) (context : Context) (args : Args)
    (w u : WGWorld) (a b : Ambient) (history : List E) (datagram : SentDatagram)
    (front : (args.beforeAppend.run w).run a = .ok ((.ok datagram,u),b))
    (next : Int → WGPrefix E α) (appends : ∀ result, StateAppends (next result)) :
    ∃ suffix, (runWGPrefix (socket record context args >>= next) w a history).2 =
      history ++ record ⟨context,args,⟨0,w,{u with sent := u.sent ++ [datagram]},a,b⟩⟩ :: suffix := by
  let after := {u with sent := u.sent ++ [datagram]}
  let event := record ⟨context,args,⟨0,w,after,a,b⟩⟩
  obtain ⟨suffix,grown⟩ := appends 0 after b (history ++ [event])
  refine ⟨suffix,?_⟩
  change (runStatePrefix (socket record context args >>= next) w a history).2 = _
  rw [runStatePrefix_bind]
  have run := append_receipt record context args w u a b history datagram front
  change runStatePrefix (socket record context args) w a history = _ at run
  rw [run]
  change (runStatePrefix (next 0) after b (history ++ [event])).2 = _
  change (runStatePrefix (next 0) after b (history ++ [event])).2 = (history ++ [event]) ++ suffix at grown
  rw [grown]
  simp only [List.append_assoc,List.singleton_append]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
