import Leanux.Proofs.WG.RetirementSecurity.HolderPollCleanup

/-! GRO's original product callbacks retain the selected RX key loan while
they can allocate and stage unrelated TX packets. The callback uses the
independent native physical and session support, including current-key
compatibility supplied by the actual receive carrier account. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open RxJoint PollCarrier DurableHolders

def GroReady (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger) (w : World) :=
  StackOwnership.Ready temporary locals active w.wg ∧ Support sessions locals active w.wg

theorem gro_stack (packets : List (List UInt8)) :
    Preserves (GroReady sessions locals active temporary) (packets.forM Env.deliverInner) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ⟨(hoare_iff_run _ _ _).mp (StackOwnership.stackForM_stack packets) w result v before.1 run,
    (hoare_iff_run _ _ _).mp (stack packets) w result v before.2 run⟩

theorem gro_receive (g : GroState) (bytes : List UInt8) :
    Preserves (GroReady sessions locals active temporary)
      (napiGroReceive (fun xs=>xs.forM Env.deliverInner) g bytes) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
    _ _ gro_stack g bytes

theorem gro_flush (g : GroState) : Preserves (GroReady sessions locals active temporary)
    (napiGroFlushAll (fun xs=>xs.forM Env.deliverInner) g) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
    _ _ gro_stack g

theorem receive_phase (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (g : Gro) (entry : Entry) :
    PrefixPreserves
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans))
      (fun _=>True) (receive g entry) := by
  apply extend (receive_appends g entry) (receive_bare_accounted initial loans pid skb stamp g entry)
  intro w h result v old before run
  obtain ⟨holders,aligned,⟨o,owner,stampEq,carriers⟩,stable⟩ := old
  obtain ⟨allocation,slot,keys⟩ := before.1
  have native : (napiGroReceive (fun xs=>xs.forM Env.deliverInner) g.erase entry.tag.bytes).run w=
      .ok (result.erase,v) := by
    have erase := projected_erases (receive_gro g entry) (napiGroReceiveTagged_erases g.forget entry.tag) w h
    rw [run] at erase
    exact erase.symm
  have post := (hoare_iff_run _ _ _).mp (gro_receive g.erase entry.tag.bytes) w result.erase v
    (show GroReady sessions locals active (allocation::temporary) w from
      ⟨⟨⟨keys,before.2.1.2⟩,before.2.1.1,carriers.keys.2⟩,before.2⟩) native
  exact ⟨⟨allocation,slot,post.1.1.1⟩,post.2⟩

theorem option_phase (initial : Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (g : Gro) (out : Option Entry) :
    PrefixPreserves
      (WithLocal sessions locals active pkt temporary
        (Accounted (fun ls h w=>Bare initial ls pid skb stamp h w ∧ StableAt initial h w) loans))
      (fun _=>True)
      (forIn out.toList g (fun entry current=>do let next←receive current entry; pure (.yield next))) := by
  cases out with
  | none=>exact PrefixEnsures.pure (fun _ _ _=>True.intro) (fun _ _ before=>before)
  | some entry=>
    simpa only [Option.toList_some,List.forIn_cons,List.forIn_nil,bind_assoc,pure_bind,bind_pure] using
      receive_phase initial loans pid skb stamp pkt g entry

theorem flush_phase (initial : Ledger) (loans : Reservations) (g : Gro) :
    PrefixPreserves
      (WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans))
      (fun _=>True) (flushAll g) := by
  apply extend (flushAll_appends g) (flush_context_accounted [] initial loans g)
  intro w h result v old before run
  cases result
  obtain ⟨holders,aligned,carriers,stable⟩ := old
  have native : (napiGroFlushAll (fun xs=>xs.forM Env.deliverInner) g.erase).run w=.ok ((),v) := by
    have erase := projected_erases (flushAll_gro g) (napiGroFlushAllTagged_erases g.forget).to_projected w h
    rw [run] at erase
    exact erase.symm
  have post := (hoare_iff_run _ _ _).mp (gro_flush g.erase) w () v
    (show GroReady sessions locals active temporary w from
      ⟨⟨⟨before.1,before.2.1.2⟩,before.2.1.1,carriers.keys.2⟩,before.2⟩) native
  exact ⟨post.1.1.1,post.2⟩

theorem complete_points (pid : PeerId) : SameView ownershipPointView (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold completeRxQueue
  repeat' ownership_source_step initial

theorem complete_phase (initial : Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures
      (WithKeys sessions locals active temporary
        (Accounted (fun ls h w=>Ready initial ls h w ∧ StableAt initial h w ∧ ColdHead pid w.wg) loans))
      (fun _=>True) (access (liftWGObserver (completeAccess pid)))
      (fun _=>WithKeys sessions locals active temporary (Accounted (StableBoundary initial) loans)) := by
  apply extend (access_appends _) (complete_accounted initial loans pid)
  intro w h result v _ before run
  have native := native_receipt
    ((access_erases (liftWGObserver_erases (completeAccess_erases pid)) w h).symm.trans run)
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp (complete_points pid)
      w.wg w.ambient result v.wg v.ambient native),
    (hoare_iff_run_ambient _ _ _).mp (complete pid) w.wg w.ambient result v.wg v.ambient before.2 native⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderPoll
