import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial

/-! Actual reservation and allocation callbacks establish the material bank.
The reservation witness is the receipt recorded immediately after its nonce
token; its immutable core is preserved up to the actual allocation entry. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity Responder ReservationAssignments Lifetimes

theorem reserve_pool (slot : KeypairId) : SameView pool (Nonce.reserveNative slot) := by
  intro initial
  unfold Nonce.reserveNative
  apply coreUpdateThen (fun p => p = initial) slot (fun k => {k with sendingCounter := k.sendingCounter + 1})
  · intro k; rfl
  · intro k; exact preserves_pure _

def Fresh (h : List Journal.Event) (packets : List DataPacket) (slot nonce : Nat) (w : WGWorld) : Prop :=
  ∃ h0 r token, h = h0 ++ [.nonce token,.reserved slot r] ∧ Packets h0 packets r.before ∧
    ReservationReceipts.Token slot r token ∧ r.value = nonce ∧ pool w = pool r.before

theorem Fresh.old (fresh : Fresh h packets slot nonce w) : Packets h packets w := by
  obtain ⟨h0,r,token,rfl,before,_,_,same⟩ := fresh
  exact before.transport (by
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl) (by rw [same]; exact Responder.Retains.refl _)

theorem Fresh.append (fresh : Fresh h packets slot nonce w) (packet : DataPacket)
    (key : packet.keypair = slot) (counter : packet.nonce = nonce) : Packets h (packets ++ [packet]) w := by
  obtain ⟨h0,r,token,rfl,before,tokenValid,value,same⟩ := fresh
  let u : Use := ⟨packet,h0.length,token,r⟩
  let suffix : List Journal.Event := [.nonce token,.reserved slot r]
  have quiet : ∀ e ∈ suffix, ReservationHistory.allocation? e = none := by
    intro e member
    simp only [suffix,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  have valid : u.Valid (h0 ++ suffix) := by
    refine ⟨?_,?_,?_,?_⟩
    · simp [u,suffix]
    · simpa only [u,key] using tokenValid
    · simpa only [u,counter] using value
    · simp [u,suffix,key]
  obtain ⟨uses,mapped,ordered,entries⟩ := before
  refine ⟨uses ++ [u],by simp only [List.map_append,List.map_cons,List.map_nil,mapped,u],?_,?_⟩
  · rw [List.map_append,List.pairwise_append]
    refine ⟨ordered,by simp,?_⟩
    intro index member other singleton
    have equal : other = u.position := by simpa using singleton
    obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp member
    rw [equal]
    exact (entries entry inside).1.bound
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · obtain ⟨entryValid,available,material⟩ := entries entry old
      exact ⟨entryValid.append,available.append quiet,by rw [same]; exact material⟩
    · have equal := List.mem_singleton.mp new
      subst entry
      exact ⟨valid,Available.fresh quiet,by rw [same]; exact fun _ resident => resident⟩

theorem reserve (slot : KeypairId) (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h w => Packets h packets w)) Safe (Journal.reserve slot)
      (fun nonce h w _ => Safe h ∧ Fresh h packets slot nonce w) := by
  have inner : StatePrefixPreserves (Keep (fun h w => Packets h packets w)) Safe
      (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)) :=
    quiet (StateAppends.focus _ _ _)
      (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((Nonce.reserveObserved slot).run w))
      (focusStatePrefix_erases _ _ (Nonce.reserveObserved_erases slot))
      (ResidentMaterial.core_of_same (reserve_pool slot))
      (fun _ _ _ _ quiet same before => before.transport quiet same)
  have capture : StatePrefixEnsures (Keep (fun h w => Packets h packets w)) Safe
      (captureWGObserved (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot)))
      (fun r h w _ => Safe h ∧ r.after = w ∧ ∃ h0 token, h = h0 ++ [.nonce token] ∧
        Packets h0 packets r.before ∧ ReservationReceipts.Token slot r token) := by
    apply (StatePrefixEnsures.captureWGObserved inner).consequence (fun _ _ _ hi => hi)
    intro r h w a post
    obtain ⟨after,_,kept,h0,before,run⟩ := post
    have erased := focusStatePrefix_erases Journal.Event.nonce Journal.nonce?
      (Nonce.reserveObserved_erases slot) r.before r.ambientBefore h0
    change (runWGPrefix (focusStatePrefix Journal.Event.nonce Journal.nonce? (Nonce.reserveObserved slot))
      r.before r.ambientBefore h0).1 = _ at erased
    rw [run] at erased
    obtain ⟨token,same,recorded⟩ := ReservationReceipts.observed slot r erased.symm h0
    rw [run] at recorded
    exact ⟨kept.1,after,h0,token,congrArg Prod.snd recorded,before.2,same⟩
  unfold Journal.reserve receiptWGObserved
  apply StatePrefixEnsures.bind capture
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h w _ => Safe h ∧ Fresh h packets slot r.value w)
  · apply StatePrefixEnsures.emit (Journal.Event.reserved slot r)
    · intro h w a hi
      exact hi.1.quiet rfl
    · intro h w a hi
      refine ⟨hi.1.quiet rfl,?_⟩
      obtain ⟨after,h0,token,rfl,before,same⟩ := hi.2
      refine ⟨h0,r,token,by simp only [List.append_assoc,List.cons_append,List.nil_append],before,same,rfl,?_⟩
      rw [←after]
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (reserve_pool slot)
        r.before r.ambientBefore r.value r.after r.ambientAfter same.1
  · intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem allocate (packets : List DataPacket) :
    StatePrefixEnsures (Keep (fun h w => Packets h packets w)) Safe (Journal.allocate packets)
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

end Leanux.Proofs.WG.HandshakeSecurity.StagingMaterial
