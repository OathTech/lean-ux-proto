import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialConfirmation

/-! Extra state and confirmation history travel through the same indexed
poll as its replay certificate. Native erasure is used only for key bounds. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder TransmitSecurity

def Framed (P : List Journal.Event → World → Prop) (h : List Journal.Event) (w : World) : Prop :=
  P h w ∧ KeyBounds w.wg ∧ Confirmation.Safe h

abbrev Base := Framed (Replay.Inv Journal.origin? Journal.replay?)
abbrev Picked (skb : SkbId) (pkt : RxPacket) := Framed (Replay.Picked Journal.origin? Journal.replay? skb pkt)
abbrev AtCounter (pkt : RxPacket) (result : Bool) :=
  Framed (Replay.AtCounter Journal.origin? Journal.replay? Journal.Event.replay pkt result)

theorem Base.carrier (hi : Base h w) : Carrier h w.wg := ⟨⟨hi.1.1,hi.2.1⟩,hi.1.2,hi.2.2⟩
theorem Carrier.base (hi : Carrier h w.wg) : Base h w := ⟨hi.replay,hi.1.2,hi.2.2⟩
theorem Base.safe (hi : Base h w) : Safe h := ⟨hi.1.2,hi.2.2⟩
theorem Picked.safe (hi : Picked skb pkt h w) : Safe h := ⟨hi.1.1.2,hi.2.2⟩
theorem AtCounter.safe (hi : AtCounter pkt result h w) : Safe h := ⟨hi.1.1.2,hi.2.2⟩

theorem Base.wg (same : w.wg = v.wg) (hi : Base h w) : Base h v :=
  ⟨⟨same ▸ hi.1.1,hi.1.2⟩,same ▸ hi.2.1,hi.2.2⟩

theorem Picked.wg (same : w.wg = v.wg) (hi : Picked skb pkt h w) : Picked skb pkt h v :=
  ⟨⟨⟨same ▸ hi.1.1.1,hi.1.1.2⟩,same ▸ hi.1.2⟩,same ▸ hi.2.1,hi.2.2⟩

theorem AtCounter.wg (same : w.wg = v.wg) (hi : AtCounter pkt result h w) : AtCounter pkt result h v := by
  obtain ⟨entry,pre,r,position,packet,value,certified,cell⟩ := hi.1
  exact ⟨⟨⟨same ▸ entry.1,entry.2⟩,pre,r,position,packet,value,certified,same ▸ cell⟩,
    same ▸ hi.2.1,hi.2.2⟩

theorem framed {g : PrefixM Journal.Event α} {action : Leanux.M α}
    (contract : PrefixEnsures P (Replay.Safe Journal.origin? Journal.replay?) g Q)
    (erase : ErasesPrefix g action)
    (bounds : Preserves (fun w : World => KeyBounds w.wg) action)
    (history : Driver.ProductHistorySafe Confirmation.Safe g) :
    PrefixEnsures (Framed P) Safe g (fun value => Framed (Q value)) := by
  intro w h hi
  obtain ⟨suffix,appended,replayed,normal⟩ := contract w h hi.1
  obtain ⟨_,_,confirmed,_⟩ := history w h hi.2.2
  refine ⟨suffix,appended,⟨replayed,confirmed⟩,?_⟩
  cases run : (runPrefix g w h).1 with
  | error err => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have native := (erase w h).symm.trans run
    have kept := (hoare_iff_run _ _ _).mp bounds w value v hi.2.1 native
    exact ⟨by simpa only [run] using normal,kept,confirmed⟩

theorem confirmation_history_native (action : Leanux.M α) :
    Driver.ProductHistorySafe Confirmation.Safe (liftPrefix action) :=
  Driver.History.product_lift action

theorem framed_native (action : WG.M α)
    (contract : PrefixEnsures P (Replay.Safe Journal.origin? Journal.replay?)
      (liftPrefix (liftWG action)) Q) (bounds : Preserves KeyBounds action) :
    PrefixEnsures (Framed P) Safe (liftPrefix (liftWG action)) (fun value => Framed (Q value)) :=
  framed contract (erasesPrefix_lift _) (PublicationPoll.native_product _ _ bounds)
    (confirmation_history_native _)

theorem poll_native (action : WG.M α) (frame : ∀ h, Preserves (Inv h) action)
    (bounds : Preserves KeyBounds action) : PrefixPreserves Base Safe (liftPrefix (liftWG action)) :=
  framed_native action (Replay.native action frame) bounds

theorem picked_native (action : WG.M α) (packets : SameView RxDisposition.nativeRxStore action)
    (frame : ∀ h, Preserves (Inv h) action) (bounds : Preserves KeyBounds action) :
    PrefixPreserves (Picked skb pkt) Safe (liftPrefix (liftWG action)) :=
  framed_native action (Replay.picked_native action packets frame) bounds

theorem atCounter_native (action : WG.M α) (packets : SameView RxDisposition.nativeRxStore action)
    (frame : ∀ h, Preserves (Inv h) action) (bounds : Preserves KeyBounds action) :
    PrefixPreserves (AtCounter pkt result) Safe (liftPrefix (liftWG action)) :=
  framed_native action (Replay.atCounter_native action packets frame) bounds

theorem read_selected (skb : SkbId) :
    PrefixEnsures Base Safe (liftPrefix (liftWG (getRxSkb skb))) (Picked skb) :=
  framed_native _ (Replay.read_selected skb) (key_bounds_skb _)

theorem counter_returned (skb : SkbId) (pkt : RxPacket) (crypted : pkt.state = .crypted) :
    PrefixEnsures (Picked skb pkt) Safe (TransportDriver.counter Journal.Event.replay skb pkt)
      (AtCounter pkt) := by
  apply framed
    (Replay.counter_returned Journal.origin? Journal.replay? Journal.Event.replay
      (fun _ => rfl) (fun _ => rfl) skb pkt crypted)
    (TransportDriver.counter_erases _ _ _)
    (PublicationPoll.native_product _ _ (key_bounds_counter pkt.keypair pkt.nonce))
  intro w h hi
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error err => exact ⟨[],by simp,hi,trivial⟩
  | ok out =>
    obtain ⟨value,v⟩ := out
    let r : TransportDriver.Replay := ⟨skb,pkt,⟨value,w,v⟩⟩
    have safe : Confirmation.Safe (h ++ [.replay r]) := hi.quiet (by
      intro event member pid kid receipt recorded
      obtain rfl := List.mem_singleton.mp member
      cases recorded)
    exact ⟨[.replay r],rfl,safe,safe⟩

macro "receive_material_bounds_frame" : tactic => `(tactic| (
  try simp (config := {zeta := false}) only [WG.andM,branch,branchCmp,invariant,unsupported]
  repeat' first
    | (rx_retention_head getPeer; exact key_bounds_read_peer _)
    | (rx_retention_head setPeer; exact key_bounds_set_peer _ _)
    | (rx_retention_head getRxSkb; exact key_bounds_skb _)
    | (rx_retention_head freeRxSkb; exact key_bounds_skb _)
    | (rx_retention_head peerPut; exact key_bounds_peer_put _)
    | (rx_retention_head keypairPut; exact key_bounds_key_put _ _)
    | (rx_retention_head PrevQueue.peek; exact key_bounds_store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head endpointFromSkb; exact key_bounds_store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head getDev; exact key_bounds_store getDev_sameWGStore)
    | (first | rx_retention_head MonadLift.monadLift | rx_retention_head MonadLiftT.monadLift
       exact hoare_liftAmbient _ _)
    | (rx_retention_head Pure.pure; exact preserves_pure _)
    | (rx_retention_head Bind.bind; apply preserves_bind)
    | (rx_retention_head ite; split)
    | keypairs_intro_forall
    | rx_retention_step))

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
