import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentHistory

/-! Actual native reservation callbacks create a fresh positional credit; only
allocation closes the current interval of credits. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 400000

def Fresh (h : List Journal.Event) (packets : List DataPacket) (slot nonce : Nat) : Prop :=
  ∃ h0 r token, h = h0 ++ [.nonce token,.reserved slot r] ∧ Packets h0 packets ∧
    ReservationReceipts.Token slot r token ∧ r.value = nonce

theorem Fresh.old (fresh : Fresh h packets slot nonce) : Packets h packets := by
  obtain ⟨h0,r,token,rfl,before,_,_⟩ := fresh
  exact before.append_history (by intro e member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl | rfl <;> rfl)

theorem Fresh.append (fresh : Fresh h packets slot nonce) (packet : DataPacket)
    (key : packet.keypair = slot) (counter : packet.nonce = nonce) : Packets h (packets ++ [packet]) := by
  obtain ⟨h0,r,token,rfl,before,same,value⟩ := fresh
  let u : Use := ⟨packet,h0.length,token,r⟩
  apply Packets.append_fresh (u := u) before
  · intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_,?_,?_⟩
    · simp [u]
    · simpa only [u,key] using same
    · simpa only [u,counter] using value
  · rfl

theorem reserve (slot : KeypairId) (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h => Packets h packets)) Safe (Journal.reserve slot)
      (fun nonce h _ _ => Safe h ∧ Fresh h packets slot nonce) := by
  have inner : StatePrefixPreserves (Keep (fun h => Packets h packets)) Safe
      (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)) :=
    quiet (StateAppends.focus _ _ _)
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w))
      (fun _ _ quiet before => before.append_history quiet)
  have capture : StatePrefixEnsures (Keep (fun h => Packets h packets)) Safe
      (captureWGObserved (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)))
      (fun r h _ _ => Safe h ∧ ∃ h0 token, h = h0 ++ [.nonce token] ∧
        Packets h0 packets ∧ ReservationReceipts.Token slot r token) := by
    apply (StatePrefixEnsures.captureWGObserved inner).consequence (fun _ _ _ hi => hi)
    intro r h w a post
    obtain ⟨_,_,kept,h0,before,run⟩ := post
    have erased := focusStatePrefix_erases Journal.Event.nonce Journal.nonce?
      (Nonce.reserveObserved_erases slot) r.before r.ambientBefore h0
    change (runWGPrefix (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot))
      r.before r.ambientBefore h0).1 = _ at erased
    rw [run] at erased
    obtain ⟨token,same,recorded⟩ := ReservationReceipts.observed slot r erased.symm h0
    rw [run] at recorded
    exact ⟨kept.1,h0,token,congrArg Prod.snd recorded,before.2,same⟩
  unfold Journal.reserve receiptWGObserved
  apply StatePrefixEnsures.bind capture
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => Safe h ∧ Fresh h packets slot r.value)
  · apply StatePrefixEnsures.emit (Journal.Event.reserved slot r)
    · intro h w a hi
      exact hi.1.quiet rfl
    · intro h w a hi
      refine ⟨hi.1.quiet rfl,?_⟩
      obtain ⟨h0,token,rfl,before,same⟩ := hi.2
      exact ⟨h0,r,token,by simp only [List.append_assoc,List.cons_append,List.nil_append],before,same,rfl⟩
  · intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem allocate (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h => Packets h packets)) Safe (Journal.allocate packets)
      (fun _ h _ _ => Safe h) := by
  intro w a h hi
  unfold Journal.allocate
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,hi.1,True.intro⟩
  | ok out =>
    obtain ⟨⟨items,v⟩,b⟩ := out
    let r : WGRunWitness (List SkbId) := ⟨items,w,v,a,b⟩
    have safe : Safe (h ++ [.allocated packets r]) := by
      apply hi.1.append
      intro pre event post position
      cases pre with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at position
        obtain ⟨same,_⟩ := position
        subst event
        exact ⟨run,by simpa only [List.append_nil] using hi.2⟩
      | cons e es =>
        have sizes := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at sizes
        omega
    exact ⟨[.allocated packets r],rfl,safe,safe⟩

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
