import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendSource

/-! Exact projection from completed protocol-socket receipts to the direct
native append source. The equality covers the error prefix, refused route,
actual append, and every input history, with no successful-return premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem protocol_projects (decode : E → Option Event)
    (record : ProtocolSocket.Receipt Context → E)
    (selected : ∀ receipt, decode (record receipt) =
      ofSent receipt.run.before.sent receipt.run.after.sent)
    (context : Context) (args : ProtocolSocket.Args) :
    StateProjectsPrefix decode id (ProtocolSocket.socket record context args) (socket args) := by
  intro w a history
  change runWGPrefix (socket args) w a (history.filterMap decode) =
    ((runWGPrefix (ProtocolSocket.socket record context args) w a history).1.map
      (fun ((value,v),b) => ((value,v),b)),
      (runWGPrefix (ProtocolSocket.socket record context args) w a history).2.filterMap decode)
  unfold ProtocolSocket.socket
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,socket_run,
    ProtocolSocket.append_factor,native_bind_run]
  cases front : (args.beforeAppend.run w).run a with
  | error stop => rfl
  | ok result =>
    obtain ⟨⟨result,u⟩,b⟩ := result
    have unchanged : u.sent = w.sent :=
      (ProjectedAction.iff_run_ambient _ _ _).mp (ProtocolSocket.beforeAppend_sent args)
        w a result u b front
    cases result with
    | error err =>
      change (Except.ok (ε := Stop) ((err,u),b),history.filterMap decode) =
        (Except.ok (ε := Stop) ((err,u),b),(history ++ [record ⟨context,args,⟨err,w,u,a,b⟩⟩]).filterMap decode)
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,selected,unchanged,
        ofSent_same,List.append_nil]
    | ok datagram =>
      change (Except.ok (ε := Stop) (((0 : Int),{u with sent := u.sent ++ [datagram]}),b),
        history.filterMap decode ++ [⟨u.sent,datagram⟩]) =
        (Except.ok (ε := Stop) (((0 : Int),{u with sent := u.sent ++ [datagram]}),b),
          (history ++ [record ⟨context,args,⟨0,w,{u with sent := u.sent ++ [datagram]},a,b⟩⟩]).filterMap decode)
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,selected,unchanged,
        ofSent_append]

def buffer (pid : PeerId) (bytes : List UInt8) : WGPrefix Event Unit :=
  ProtocolSocket.bufferWith liftWGPrefix socket pid bytes

theorem buffer_projects (decode : E → Option Event)
    (record : ProtocolSocket.Receipt (CausalEffects.Context Cause) → E)
    (selected : ∀ receipt, decode (record receipt) =
      ofSent receipt.run.before.sent receipt.run.after.sent)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) :
    StateProjectsPrefix decode id (ProtocolSocket.observed record scope pid bytes) (buffer pid bytes) := by
  apply ProtocolSocket.buffer_projects decode
  · intro α action w a history
    change ((action.run w).run a,history.filterMap decode) =
      (((action.run w).run a).map (fun ((value,v),b) => ((value,v),b)),history.filterMap decode)
    cases (action.run w).run a <;> rfl
  · intro args
    exact CausalEffects.atCurrent_projects scope _ decode _
      (fun context => protocol_projects decode record selected context args)

theorem buffer_erases (pid : PeerId) (bytes : List UInt8) :
    ErasesStatePrefix (buffer pid bytes) (sendBufferToPeer pid bytes) :=
  ProtocolSocket.buffer_erases liftWGPrefix socket erasesStatePrefix_lift socket_erases pid bytes

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
