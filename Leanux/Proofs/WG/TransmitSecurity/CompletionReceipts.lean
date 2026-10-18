import Leanux.Proofs.WG.TransmitSecurity.CompletionSource
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! Actual TX packet/peer/socket witnesses survive the completion suffix and
its possible Stop. No initialized packet-ownership premise is hidden here. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Good (h : List Event) : Prop := ∀ r ∈ h.filterMap socket?, r.Valid

private theorem unchanged_safe {g : PrefixM Event α} (append : Appends g)
    (frame : HistoryFrame socket? g) : PrefixPreserves (fun h _ => Good h) Good g := by
  intro w h hi
  obtain ⟨suffix,eq⟩ := append w h
  have good : Good (runPrefix g w h).2 := by
    unfold Good
    rw [frame w h]
    exact hi
  refine ⟨suffix,eq,good,?_⟩
  cases (runPrefix g w h).1 <;> trivial

private theorem access_safe (a : MixedM α) :
    PrefixPreserves (fun h _ => Good h) Good (access a) :=
  unchanged_safe (Appends.focus _ _ _)
    (focusPrefix_other _ _ _ (fun _ => rfl) _)

private theorem focus_safe (a : PrefixM TxDisposition.Event α) :
    PrefixPreserves (fun h _ => Good h) Good
      (focusPrefix Event.disposition disposition? a) :=
  unchanged_safe (Appends.focus _ _ _) (focusPrefix_other _ _ _ (fun _ => rfl) _)

private theorem lift_safe (a : Leanux.M α) :
    PrefixPreserves (fun h _ => Good h) Good (liftPrefix a) :=
  unchanged_safe (Appends.lift a) (HistoryFrame.lift _ a)

private theorem disposition_safe (e : TxDisposition.Event) :
    PrefixPreserves (fun h (_ : World) => Good h) Good (emitPrefix (.disposition e)) :=
  unchanged_safe (fun _ _ => ⟨[.disposition e],rfl⟩) (HistoryFrame.emit _ rfl)

private theorem capture_safe {g : PrefixM Event α} {a : Leanux.M α}
    (safe : PrefixPreserves (fun h _ => Good h) Good g) (erases : ErasesPrefix g a) :
    PrefixEnsures (fun h _ => Good h) Good (captureObserved g)
      (fun r h _ => Good h ∧ r.Valid a) := by
  have ensure : PrefixEnsures (fun h _ => Good h) Good g (fun _ h _ => Good h) := safe
  apply (PrefixEnsures.captureObserved ensure).consequence
  · intro _ _ hi; exact hi
  · intro r h v out
    obtain ⟨h0,_,run⟩ := out.2.2
    have native := erases r.before h0
    rw [run] at native
    exact ⟨out.2.1,native.symm⟩

private theorem emit_socket_safe (r : SocketReceipt) (valid : r.Valid) :
    PrefixPreserves (fun h (_ : World) => Good h) Good (emitPrefix (.socket r)) := by
  intro w h hi
  have good : Good (h ++ [.socket r]) := by
    intro q member
    simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      socket?,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with old | rfl
    · exact hi q old
    · exact valid
  exact ⟨[.socket r],rfl,good,good⟩

theorem socket_safe (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool)
    (packetValid : packet.Valid (liftWG (getTxSkb id)))
    (peerValid : peer.Valid (liftWG (getPeer pid))) :
    PrefixPreserves (fun h _ => Good h) Good (socket pid id packet peer ipv4) := by
  unfold socket receiptObserved
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture_safe
    (a := liftWG (if ipv4 then send4 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
      (some pid) packet.value.bytes packet.value.ds true
      else send6 (peer.value.endpoint.getD {family := 0,addr := 0,port := 0})
      (some pid) packet.value.bytes packet.value.ds true))
    (by cases ipv4 <;> exact access_safe _)
    (by cases ipv4
        · exact access_erases (send6Prefix_erases _ _ _ _ _)
        · exact access_erases (send4Prefix_erases _ _ _ _ _)))
  intro run w h hi
  have valid : (SocketReceipt.mk pid id packet peer ipv4 run).Valid := by
    refine ⟨packetValid,peerValid,?_⟩
    cases ipv4 <;> exact hi.2
  exact PrefixPreserves.bind (emit_socket_safe _ valid)
    (fun _ => PrefixPreserves.pure (fun h (_ : World) (good : Good h) => good) run.value) w h hi.1

macro "completion_good_step" : tactic => `(tactic| first
  | (nonce_product_head access; exact access_safe _)
  | (nonce_product_head liftPrefix; exact lift_safe _)
  | (nonce_product_head emitPrefix; exact disposition_safe _)
  | (nonce_product_head focusPrefix; exact focus_safe _)
  | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun h (_ : World) (hi : Good h) => hi) _)
  | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
  | (nonce_product_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun h (_ : World) (hi : Good h) => hi))
  | (nonce_product_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem send_safe (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (packetValid : packet.Valid (liftWG (getTxSkb id))) :
    PrefixPreserves (fun h _ => Good h) Good (send pid id packet) := by
  unfold send
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture_safe (access_safe _) (access_erases (getPeerMixed_erases _)))
  intro peer w h hi
  apply (show PrefixPreserves (fun h _ => Good h) Good _ from ?_) w h hi.1
  repeat' first
    | (nonce_product_head socket; exact socket_safe _ _ _ _ _ packetValid hi.2)
    | completion_good_step


private theorem packet_continuation_safe (id : SkbId) (f : RunWitness DataPacket → PrefixM Event α)
    (safe : ∀ r, r.Valid (liftWG (getTxSkb id)) → PrefixPreserves (fun h _ => Good h) Good (f r)) :
    PrefixPreserves (fun h _ => Good h) Good (captureObserved (access (getTxSkbPrefix id)) >>= f) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (capture_safe (access_safe _) (access_erases (getTxSkbPrefix_erases _)))
  intro r w h hi
  exact safe r hi.2 w h hi.1

theorem complete_safe (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (fun h _ => Good h) Good (complete pid item) := by
  unfold complete TxDisposition.andObs
  repeat' first
    | (nonce_product_head Bind.bind
       with_reducible apply packet_continuation_safe
       intro packet valid
       repeat' first
         | (nonce_product_head send; exact send_safe _ _ _ valid)
         | completion_good_step)
    | completion_good_step

theorem body_safe (pid : PeerId) (first : Option (List SkbId)) :
    PrefixPreserves (fun h _ => Good h) Good (body pid first) := by
  unfold body TxDisposition.andObs
  repeat' first
    | (nonce_product_head complete; exact complete_safe _ _)
    | completion_good_step

theorem step_safe (pid : PeerId) :
    PrefixPreserves (fun h _ => Good h) Good (step pid) := by
  unfold step
  repeat' first
    | (nonce_product_head body; exact body_safe _ _)
    | completion_good_step

theorem step_receipts (pid : PeerId) (w : World) : Good (runPrefix (step pid) w []).2 := by
  obtain ⟨_,_,safe,_⟩ := step_safe pid w [] (by intro r member; simp at member)
  exact safe


theorem step_appends (pid : PeerId) : Appends (step pid) := by
  unfold step body complete send socket receiptObserved TxDisposition.andObs
  repeat' first
    | with_reducible exact Appends.focus _ _ _
    | (change Appends (focusPrefix _ _ _); exact Appends.focus _ _ _)
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | (change Appends (emitPrefix _); exact fun _ _ => ⟨[_],rfl⟩)
    | with_reducible apply Appends.captureObserved
    | with_reducible apply Appends.bind
    | with_reducible apply Appends.forIn
    | (with_reducible intro x; try dsimp only)
    | dsimp (config := {failIfUnchanged := true}) only
    | split

end Leanux.Proofs.WG.TransmitSecurity.Completion
