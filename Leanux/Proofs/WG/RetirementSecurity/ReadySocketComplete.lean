import Leanux.Proofs.WG.RetirementSecurity.ReadySocketFrames

/-! Every actual socket receipt in native completion has nonempty bytes.
The selected complete batch supplies this at each getter; all intervening
source effects preserve the actual packet cells, including stopped prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadySocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Completion ReadyCiphertext
set_option maxHeartbeats 600000

private theorem capture {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (safe : PrefixPreserves (Inv (Complete items)) (Good) g) (erases : ErasesPrefix g a) :
    PrefixEnsures (Inv (Complete items)) (Good) (captureObserved g)
      (fun r h w => Inv (Complete items) h w ∧ r.Valid a ∧ r.after = w) := by
  apply (PrefixEnsures.captureObserved safe).consequence
  · intro _ _ hi; exact hi
  · intro r h v out
    obtain ⟨h0,_,run⟩ := out.2.2
    have native := erases r.before h0
    rw [run] at native
    exact ⟨out.1 ▸ out.2.1,native.symm,out.1⟩

private theorem emit_socket (r : SocketReceipt) (origin : r.packet.value.bytes≠[]) :
    PrefixPreserves (Inv (Complete items)) (Good) (emitPrefix (.socket r)) := by
  intro w h before
  have good : Good (h ++ [.socket r]) := by
    intro q member
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Completion.socket?,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with old | rfl
    · exact before.2 q old
    · exact origin
  exact ⟨[.socket r],rfl,good,before.1,good⟩

theorem socket (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (origin : packet.value.bytes≠[]) :
    PrefixPreserves (Inv (Complete items)) (Good) (Completion.socket pid id packet peer ipv4) := by
  unfold Completion.socket receiptObserved
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture
    (a := liftWG (if ipv4 then WG.send4 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
      (some pid) packet.value.bytes packet.value.ds true
      else WG.send6 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
      (some pid) packet.value.bytes packet.value.ds true))
    (by cases ipv4
        · exact access (send6Prefix_erases _ _ _ _ _) (send6 _ _ _ _ _)
        · exact access (send4Prefix_erases _ _ _ _ _) (send4 _ _ _ _ _))
    (by cases ipv4
        · exact Completion.access_erases (send6Prefix_erases _ _ _ _ _)
        · exact Completion.access_erases (send4Prefix_erases _ _ _ _ _)))
  intro run w h before
  exact PrefixPreserves.bind (emit_socket ⟨pid,id,packet,peer,ipv4,run⟩ origin)
    (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) run.value) w h before.1

macro "ready_socket_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.access; first
      | exact access (getPeerMixed_erases _) (complete_frame (packets_peer _))
      | exact access (modifyPeerKeysPrefix_erases _ _) (complete_frame (peer_modify _ _))
      | exact access (timersTraversalPrefix_erases _) (wire (timersTraversal_cryptWire _))
      | exact access (timersAnyAuthenticatedPacketSentPrefix_erases _) (authenticated_sent _)
      | exact access (timersDataSentPrefix_erases _) (wire (timersDataSent_cryptWire _))
      | exact access (keepKeyFreshPrefix_erases _) (wire (keepKeyFresh_cryptWire _)))
  | (nonce_product_head liftPrefix; first
      | exact ReadySocket.branch _ _
      | exact ambient _)
  | (nonce_product_head emitPrefix; exact disposition _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (origin : packet.value.bytes≠[]) :
    PrefixPreserves (Inv (Complete items)) (Good) (Completion.send pid id packet) := by
  unfold Completion.send
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture
    (access (getPeerMixed_erases pid) (complete_frame (packets_peer pid)))
    (Completion.access_erases (getPeerMixed_erases pid)))
  intro peer w h before
  apply (show PrefixPreserves (Inv (Complete items)) (Good) _ from ?_) w h before.1
  repeat' first
    | (nonce_product_head Completion.socket; exact socket _ _ _ _ _ origin)
    | ready_socket_step

private theorem read (id : SkbId) (member : id∈items) :
    PrefixEnsures (Inv (Complete items)) Good (captureObserved (Completion.access (getTxSkbPrefix id)))
      (fun r h w=>Inv (Complete items) h w ∧ r.value.bytes≠[]) := by
  apply (capture (access (getTxSkbPrefix_erases id) (complete_frame (packets_read id)))
    (Completion.access_erases (getTxSkbPrefix_erases id))).consequence
  · intro _ _ before; exact before
  · intro r h w before
    obtain ⟨_,resident⟩:=read_cell r before.2.1
    rw [before.2.2] at resident
    exact ⟨before.1,before.1.1 id member r.value resident⟩

private theorem loop (xs : List α) (init : β) (body : α → β → PrefixM Completion.Event (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, PrefixPreserves (Inv (Complete items)) (Good) (body x b)) :
    PrefixPreserves (Inv (Complete items)) (Good) (forIn xs init body) := by
  induction xs generalizing init with
  | nil => exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PrefixPreserves.bind (step x (by simp) init)
    intro result
    cases result with
    | done value => exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
    | yield value => exact ih value (fun y member => step y (by simp [member]))

theorem complete (pid : PeerId) (items : List SkbId) :
    PrefixPreserves (Inv (Complete items)) (Good) (Completion.complete pid items) := by
  unfold Completion.complete
  apply PrefixPreserves.bind (disposition _)
  intro _
  apply PrefixPreserves.bind (access (timersTraversalPrefix_erases pid) (wire (timersTraversal_cryptWire pid)))
  intro _
  apply PrefixPreserves.bind (access (timersAnyAuthenticatedPacketSentPrefix_erases pid) (authenticated_sent pid))
  intro _
  apply PrefixPreserves.bind
  · apply loop
    intro id member dataSent
    apply PrefixEnsures.bind (read id member)
    intro packet w h before
    apply (show PrefixPreserves (Inv (Complete items)) (Good) _ from ?_) w h before.1
    unfold TxDisposition.andObs
    repeat' first
      | (nonce_product_head Completion.send; exact send pid id packet before.2)
      | ready_socket_step
  · intro dataSent
    apply PrefixPreserves.bind (ReadySocket.branch .doneSkbIterate false)
    intro _
    apply PrefixPreserves.bind (ReadySocket.branch .doneDataSent dataSent)
    intro yes
    cases yes <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact access (keepKeyFreshPrefix_erases pid) (wire (keepKeyFresh_cryptWire pid))
    · apply PrefixPreserves.bind (access (timersDataSentPrefix_erases pid) (wire (timersDataSent_cryptWire pid)))
      intro _
      exact access (keepKeyFreshPrefix_erases pid) (wire (keepKeyFresh_cryptWire pid))

end Leanux.Proofs.WG.RetirementSecurity.ReadySocket
