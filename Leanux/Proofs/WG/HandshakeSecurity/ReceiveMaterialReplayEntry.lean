import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialReplay

/-! The exact returned counter receipt and its selected cell survive the
native guards into confirmation. The key read at that entry discharges the
carrier's conditional residency premise. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {record : TransportDriver.Replay → E}
  {pkt : RxPacket} {result : Bool}

def AtCounter (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (pkt : RxPacket) (result : Bool) (h : List E) (w : World) : Prop :=
  Inv origin replay h w ∧ ∃ pre r, h = pre ++ [record r] ∧ r.packet = pkt ∧
    r.run.value = result ∧ Certified (pre.filterMap origin) r ∧
    (RxDisposition.nativeRxStore w.wg).2 r.skb = some pkt

theorem counter_returned (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (skb : SkbId) (pkt : RxPacket) (crypted : pkt.state = .crypted) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (TransportDriver.counter record skb pkt) (AtCounter origin replay record pkt) := by
  intro w h hi
  obtain ⟨suffix,appended,safe,normal⟩ := counter_checked origin replay record inverse quiet skb pkt crypted w h hi
  refine ⟨suffix,appended,safe,?_⟩
  rw [TransportDriver.counter_run] at normal ⊢
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,v⟩
    simp only [run] at normal ⊢
    refine ⟨normal,h,⟨skb,pkt,⟨value,w,v⟩⟩,rfl,rfl,rfl,?_,?_⟩
    · obtain ⟨d,device,cell⟩ := Option.bind_eq_some_iff.mp hi.2
      obtain ⟨_,core,certificate,conditional⟩ := hi.1.1 d device skb pkt cell crypted
      exact ⟨run,⟨hi.2,crypted⟩,core,certificate,conditional⟩
    · have same := (ProjectedAction.iff_run _ _ _).mp
        (RxDisposition.counter_rxStore pkt.keypair pkt.nonce) w value v run
      exact (congrFun (congrArg Prod.snd same) skb).trans hi.2

theorem atCounter_native (action : WG.M α)
    (packets : SameView RxDisposition.nativeRxStore action)
    (frame : ∀ h, Preserves (ReceiveMaterial.Inv h) action) :
    PrefixPreserves (AtCounter origin replay record pkt result) (Safe origin replay)
      (liftPrefix (liftWG action)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
  intro h w x v hi run
  have kept := (hoare_iff_run _ _ _).mp
    (PublicationPoll.native_product _ _ (frame (h.filterMap origin))) w x v hi.1.1 run
  have product := sameView_liftWG RxDisposition.rxStore RxDisposition.nativeRxStore action packets
    (fun _ _ _ equal => equal)
  have same := (ProjectedAction.iff_run _ _ _).mp product w x v run
  obtain ⟨pre,r,position,packet,value,certificate,cell⟩ := hi.2
  refine ⟨⟨kept,hi.1.2⟩,pre,r,position,packet,value,certificate,?_⟩
  exact (congrFun (congrArg Prod.snd same) r.skb).trans cell

/-- At the native confirmation entry, a resident key has the allocation of
the exact accepted packet's earlier native AEAD, not just its numeric slot. -/
theorem AtCounter.material (input : AtCounter origin replay record pkt true h w)
    (quiet : ∀ r, origin (record r) = none)
    (resident : pool w.wg pkt.keypair = some core) :
    ∃ pre r, h = pre ++ [record r] ∧ r.packet = pkt ∧ r.run.value = true ∧
      Certified (pre.filterMap origin) r ∧ Certificate (pre.filterMap origin) r.skb pkt w.wg core := by
  obtain ⟨current,pre,r,position,packet,value,certified,cell⟩ := input
  obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp cell
  have crypted : pkt.state = .crypted := packet ▸ certified.2.1.2
  obtain ⟨_,original,certificate,conditional⟩ := current.1 d device r.skb pkt stored crypted
  have equal := conditional core resident
  subst original
  refine ⟨pre,r,position,packet,value,certified,?_⟩
  simpa only [position,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
    Option.toList_none,List.nil_append,List.append_nil] using certificate

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Replay
