import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendProtocol
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsEmbedding

/-! Transport lifetime accesses precede the same native final append. Their
events are independently quiet under the raw selector; native-result erasure
alone is not used to identify the raw append history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity

def completion? : Completion.Event → Option Event
  | .socket receipt => ofSent receipt.socket.before.wg.sent receipt.socket.after.wg.sent
  | .disposition _ => none

def transportArgs (pid : PeerId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : ProtocolSocket.Args :=
  ⟨ipv4,peer.value.endpoint.getD {family := 0,addr := 0,port := 0},
    some pid,packet.value.bytes,packet.value.ds,true⟩

theorem product_receipt_projects (decode : E → Option Event) (args : ProtocolSocket.Args)
    (body : PrefixM E Int) (erases : ErasesPrefix body (liftWG args.action))
    (quiet : HistoryFrame decode body) (record : RunWitness Int → E)
    (selected : ∀ receipt, decode (record receipt) = ofSent receipt.before.wg.sent receipt.after.wg.sent) :
    ProjectsPrefix decode id (receiptObserved body record) (liftWGObserver (socket args)) := by
  intro w history
  have result := erases w history
  have events := quiet w history
  rw [liftWG_run,ProtocolSocket.append_factor,native_bind_run] at result
  change runPrefix (liftWGObserver (socket args)) w (history.filterMap decode) = _
  change
    ((runWGPrefix (socket args) w.wg w.ambient (history.filterMap decode)).1.map
      (fun ((value,g),a) => (value,{w with wg := g,ambient := a})),
      (runWGPrefix (socket args) w.wg w.ambient (history.filterMap decode)).2) = _
  rw [socket_run,runPrefix_receiptObserved]
  generalize observed : runPrefix body w history = output at result events ⊢
  obtain ⟨outcome,suffix⟩ := output
  cases front : (args.beforeAppend.run w.wg).run w.ambient with
  | error stop =>
    simp only [front,Except.map] at result
    rw [result]
    exact Prod.ext rfl events.symm
  | ok out =>
    obtain ⟨⟨value,u⟩,b⟩ := out
    rw [front] at result
    have unchanged : u.sent = w.wg.sent :=
      (ProjectedAction.iff_run_ambient _ _ _).mp (ProtocolSocket.beforeAppend_sent args)
        w.wg w.ambient value u b front
    cases value with
    | error err =>
      change outcome = .ok (err,{w with wg := u,ambient := b}) at result
      rw [result]
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,selected,
        unchanged,ofSent_same,List.append_nil,events,Except.map]
      rfl
    | ok datagram =>
      change outcome =
        .ok (0,{w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}) at result
      rw [result]
      simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,selected,
        unchanged,ofSent_append,events,Except.map]
      rfl

theorem access_quiet (action : MixedM α) : HistoryFrame completion? (Completion.access action) :=
  focusPrefix_other _ _ completion? (fun _ => rfl) _

theorem transport_socket_projects (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) :
    ProjectsPrefix completion? id (Completion.socket pid skb packet peer ipv4)
      (liftWGObserver (socket (transportArgs pid packet peer ipv4))) := by
  unfold Completion.socket
  apply product_receipt_projects
  · cases ipv4
    · exact Completion.access_erases (send6Prefix_erases _ _ _ _ _)
    · exact Completion.access_erases (send4Prefix_erases _ _ _ _ _)
  · cases ipv4 <;> exact access_quiet _
  · intro receipt
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
