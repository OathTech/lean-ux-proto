import Leanux.Proofs.WG.TransmitSecurity.CompletionSource
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocketCut

/-! The actual transport socket cannot append and then lose its receipt to an
internal Stop. Native fallible work precedes the final append; the existing
lifetime observer and every append-only continuation retain that occurrence. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AuthenticatedEffects

private theorem receipt_forward (body : PrefixM E α) (native : Leanux.M α)
    (erases : ErasesPrefix body native) (appends : Appends body)
    (record : RunWitness α → E) (w v : World) (history : List E) (value : α)
    (run : native.run w = .ok (value,v)) :
    ∃ middle, runPrefix (receiptObserved body record) w history =
      (.ok (value,v),(history ++ middle) ++ [record ⟨value,w,v⟩]) := by
  obtain ⟨middle,grown⟩ := appends w history
  have result : (runPrefix body w history).1 = .ok (value,v) := (erases w history).trans run
  have both : runPrefix body w history = (.ok (value,v),history ++ middle) := Prod.ext result grown
  refine ⟨middle,?_⟩
  rw [runPrefix_receiptObserved,both]

def socketArgs (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : ProtocolSocket.Args :=
  ⟨ipv4,peer.value.endpoint.getD {family := 0,addr := 0,port := 0},
    some pid,packet.value.bytes,packet.value.ds,true⟩

/-- Reaching the native final append guarantees a transport socket receipt,
even though the old lifetime observer can insert events before that receipt. -/
theorem socket_append_receipt (pid : PeerId) (id : SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool)
    (w : World) (u : WGWorld) (b : Ambient) (history : List Event) (datagram : SentDatagram)
    (front : (((socketArgs pid packet peer ipv4).beforeAppend).run w.wg).run w.ambient =
      .ok ((.ok datagram,u),b)) :
    let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
    ∃ middle, runPrefix (socket pid id packet peer ipv4) w history =
      (.ok (0,v),(history ++ middle) ++ [.socket ⟨pid,id,packet,peer,ipv4,⟨0,w,v⟩⟩]) := by
  let args := socketArgs pid packet peer ipv4
  let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
  have native : (args.action.run w.wg).run w.ambient =
      .ok ((0,{u with sent := u.sent ++ [datagram]}),b) := by
    rw [ProtocolSocket.append_factor,native_bind_run,front]
    rfl
  have product : (liftWG args.action).run w = .ok (0,v) := by
    rw [liftWG_run,native]
    rfl
  unfold socket
  apply receipt_forward _ (liftWG args.action) _ _ _ w v history 0 product
  · cases ipv4
    · exact access_erases (send6Prefix_erases _ _ _ _ _)
    · exact access_erases (send4Prefix_erases _ _ _ _ _)
  · cases ipv4 <;> exact Appends.focus _ _ _

/-- An actual transport append remains before every event of a later
continuation, including a continuation that Stops. No successful caller return
is assumed, and equal-valued datagrams retain separate receipt positions. -/
theorem socket_append_retained (pid : PeerId) (id : SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool)
    (w : World) (u : WGWorld) (b : Ambient) (history : List Event) (datagram : SentDatagram)
    (front : (((socketArgs pid packet peer ipv4).beforeAppend).run w.wg).run w.ambient =
      .ok ((.ok datagram,u),b))
    (next : Int → PrefixM Event α) (appends : ∀ value, Appends (next value)) :
    let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
    ∃ middle suffix, (runPrefix (socket pid id packet peer ipv4 >>= next) w history).2 =
      (history ++ middle) ++ .socket ⟨pid,id,packet,peer,ipv4,⟨0,w,v⟩⟩ :: suffix := by
  let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
  let event := Event.socket ⟨pid,id,packet,peer,ipv4,⟨0,w,v⟩⟩
  obtain ⟨middle,run⟩ := socket_append_receipt pid id packet peer ipv4 w u b history datagram front
  obtain ⟨suffix,grown⟩ := appends 0 v ((history ++ middle) ++ [event])
  refine ⟨middle,suffix,?_⟩
  rw [runPrefix_bind,run]
  change (runPrefix (next 0) v ((history ++ middle) ++ [event])).2 = _
  rw [grown]
  simp only [List.append_assoc,List.singleton_append]
  rfl

end Leanux.Proofs.WG.TransmitSecurity.Completion
