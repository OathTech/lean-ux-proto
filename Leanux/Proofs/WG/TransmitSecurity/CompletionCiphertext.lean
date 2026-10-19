import Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertextFrames

/-! Nonempty bytes at each actual socket packet read have an earlier native
AEAD certificate in the supplied history. Empty-cell exclusion is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Completion
set_option maxHeartbeats 600000

private theorem capture {g : PrefixM Completion.Event α} {a : Leanux.M α}
    (safe : PrefixPreserves (Inv bank) (Good bank) g) (erases : ErasesPrefix g a) :
    PrefixEnsures (Inv bank) (Good bank) (captureObserved g)
      (fun r h w => Inv bank h w ∧ r.Valid a ∧ r.after = w) := by
  apply (PrefixEnsures.captureObserved safe).consequence
  · intro _ _ hi; exact hi
  · intro r h v out
    obtain ⟨h0,_,run⟩ := out.2.2
    have native := erases r.before h0
    rw [run] at native
    exact ⟨out.1 ▸ out.2.1,native.symm,out.1⟩

private theorem emit_socket (r : SocketReceipt) (origin : ReadOrigin bank r.id r.packet) :
    PrefixPreserves (Inv bank) (Good bank) (emitPrefix (.socket r)) := by
  intro w h before
  have good : Good bank (h ++ [.socket r]) := by
    intro q member
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      Completion.socket?,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with old | rfl
    · exact before.2 q old
    · exact origin
  exact ⟨[.socket r],rfl,good,before.1,good⟩

theorem socket (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (origin : ReadOrigin bank id packet) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.socket pid id packet peer ipv4) := by
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

macro "completion_ciphertext_step" : tactic => `(tactic| first
  | (nonce_product_head Completion.access; first
      | exact access (getPeerMixed_erases _) (CiphertextOrigins.NativeFrames.read_peer _)
      | exact access (modifyPeerKeysPrefix_erases _ _) (peer_modify _ _)
      | exact access (timersTraversalPrefix_erases _) (wire (timersTraversal_cryptWire _))
      | exact access (timersAnyAuthenticatedPacketSentPrefix_erases _) (authenticated_sent _)
      | exact access (timersDataSentPrefix_erases _) (wire (timersDataSent_cryptWire _))
      | exact access (keepKeyFreshPrefix_erases _) (wire (keepKeyFresh_cryptWire _)))
  | (nonce_product_head liftPrefix; first
      | exact CompletionCiphertext.branch _ _
      | exact ambient _)
  | (nonce_product_head emitPrefix; exact disposition _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (origin : ReadOrigin bank id packet) :
    PrefixPreserves (Inv bank) (Good bank) (Completion.send pid id packet) := by
  unfold Completion.send
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture
    (access (getPeerMixed_erases pid) (CiphertextOrigins.NativeFrames.read_peer pid))
    (Completion.access_erases (getPeerMixed_erases pid)))
  intro peer w h before
  apply (show PrefixPreserves (Inv bank) (Good bank) _ from ?_) w h before.1
  repeat' first
    | (nonce_product_head Completion.socket; exact socket _ _ _ _ _ origin)
    | completion_ciphertext_step

private theorem read (id : SkbId) :
    PrefixEnsures (Inv bank) (Good bank) (captureObserved (Completion.access (getTxSkbPrefix id)))
      (fun r h w => Inv bank h w ∧ ReadOrigin bank id r) := by
  apply (capture (access (getTxSkbPrefix_erases id) (CiphertextOrigins.NativeFrames.read_packet id))
    (Completion.access_erases (getTxSkbPrefix_erases id))).consequence
  · intro _ _ before; exact before
  · intro r h w before
    obtain ⟨same,resident⟩ := CiphertextOrigins.read_cell r before.2.1
    refine ⟨before.1,?_⟩
    intro generation atEpoch nonempty
    have atAfter : PacketOrigins.epoch r.after.wg = some generation := by rw [same]; exact atEpoch
    rw [before.2.2] at atAfter resident
    exact before.1.1 generation atAfter id r.value resident nonempty

private theorem loop (xs : List α) (init : β) (body : α → β → PrefixM Completion.Event (ForInStep β))
    (step : ∀ x ∈ xs, ∀ b, PrefixPreserves (Inv bank) (Good bank) (body x b)) :
    PrefixPreserves (Inv bank) (Good bank) (forIn xs init body) := by
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
    PrefixPreserves (Inv bank) (Good bank) (Completion.complete pid items) := by
  unfold Completion.complete
  apply PrefixPreserves.bind (disposition _)
  intro _
  apply PrefixPreserves.bind (access (timersTraversalPrefix_erases pid) (wire (timersTraversal_cryptWire pid)))
  intro _
  apply PrefixPreserves.bind (access (timersAnyAuthenticatedPacketSentPrefix_erases pid) (authenticated_sent pid))
  intro _
  apply PrefixPreserves.bind
  · apply loop
    intro id _member dataSent
    apply PrefixEnsures.bind (read id)
    intro packet w h before
    apply (show PrefixPreserves (Inv bank) (Good bank) _ from ?_) w h before.1
    unfold TxDisposition.andObs
    repeat' first
      | (nonce_product_head Completion.send; exact send pid id packet before.2)
      | completion_ciphertext_step
  · intro dataSent
    apply PrefixPreserves.bind (CompletionCiphertext.branch .doneSkbIterate false)
    intro _
    apply PrefixPreserves.bind (CompletionCiphertext.branch .doneDataSent dataSent)
    intro yes
    cases yes <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact access (keepKeyFreshPrefix_erases pid) (wire (keepKeyFresh_cryptWire pid))
    · apply PrefixPreserves.bind (access (timersDataSentPrefix_erases pid) (wire (timersDataSent_cryptWire pid)))
      intro _
      exact access (keepKeyFreshPrefix_erases pid) (wire (keepKeyFresh_cryptWire pid))

end Leanux.Proofs.WG.TransmitSecurity.CompletionCiphertext
