import Leanux.Proofs.WG.Queues.RxPollJoint

/-! Direct projections of one stamped poll execution. The GRO projection is
unconditional. Access projection uses the existing allocation invariant at
entry and transports it through the exact lower observer. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem peekAccess_erases (pid : PeerId) : ErasesPrefix (peekAccess pid) (peekRxQueue pid) := by
  unfold peekAccess peekRxQueue modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem readyAccess_erases (first : Option SkbId) :
    ErasesPrefix (readyAccess first) (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  unfold readyAccess
  apply andPrefix_erases (erasesPrefix_lift _)
  cases first <;> dsimp only
  · exact erasesPrefix_lift _
  · exact erasesPrefix_bind (getRxSkbPrefix_erases _) (fun _ => erasesPrefix_lift _)

theorem completeAccess_erases (pid : PeerId) :
    ErasesPrefix (completeAccess pid) (completeRxQueue pid) := by
  unfold completeAccess completeRxQueue modifyPeerKeysPrefix
  exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _)

/-- The one original successful getter supplies both the packet and its stamp.
A failed getter contributes no read or capture. -/
theorem capture_run (id : SkbId) (w : World) (h : List Event) :
    runPrefix (capture id) w h = match (getRxSkb id).run w with
    | .error e => (.error e, h)
    | .ok (p, v) => (.ok ((p, packetStamp w id), v),
        h ++ [.access (.packet (.read (.inr id) (packetStamp w id)))]) := by
  have hr : runPrefix (access (getRxSkbPrefix id)) w h =
      match (getRxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.access (.packet (.read (.inr id) (packetStamp w id)))]) := by
    unfold access
    cases hg : (getRxSkb id).run w with
    | error e =>
      simpa only [List.map_nil, List.append_nil] using
        focusPrefix_suffix Event.access accessEvent (getRxSkbPrefix id) w h (.error e) []
          (by simp only [getRxSkbPrefix_run, hg, List.append_nil])
    | ok out => exact focusPrefix_suffix _ _ _ _ _ _ _ (by rw [getRxSkbPrefix_run, hg])
  change ((runPrefix (access (getRxSkbPrefix id)) w h).1.map _,
    (runPrefix (access (getRxSkbPrefix id)) w h).2) = _
  rw [hr]
  cases (getRxSkb id).run w <;> rfl

theorem capture_gro (id : SkbId) :
    ProjectsPrefix groEvent Prod.fst (capture id) (liftPrefix (getRxSkb id)) := by
  intro w h
  rw [capture_run, runPrefix_lift]
  cases (getRxSkb id).run w <;> simp [groEvent, List.filterMap_append, Except.map]

theorem drop_gro (pid occurrence skb : Nat) (stamp : PacketStamp) :
    ProjectsPrefix groEvent id (drop pid occurrence skb stamp) (dropGroPrefix pid occurrence skb) := by
  unfold drop dropGroPrefix
  exact projectsPrefix_bind groEvent id id (access_gro (rxDropPeekedPrefix_erases _))
    (fun _ => projectsPrefix_emit _ _)

theorem consume_gro (pid occurrence skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    ProjectsPrefix groEvent (Option.map Entry.tag) (consume pid occurrence skb stamp pkt ep)
      (consumeGro pid occurrence skb pkt ep) := by
  intro w h
  have hp := access_gro (consumeDataDonePrefix_erases pid pkt ep) w h
  simp only [consumeGro, runPrefix_bind]
  rw [hp, consume_run]
  cases runPrefix (access (consumeDataDonePrefix pid pkt ep)) w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨out, v⟩
      cases out <;> simp only [map_eq_pure_bind, runPrefix_bind, runPrefix_emit, runPrefix_pure, groEvent,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil,
        Option.map, Except.map, Prod.fst, Prod.snd, id]

theorem receiveOption_gro (g : Gro) (out : Option Entry) :
    ProjectsPrefix groEvent Gro.forget (out.elim (pure g) (receive g))
      ((out.toList.map Entry.tag).foldlM (fun g e => napiGroReceiveTagged g e) g.forget) := by
  cases out with
  | none => exact projectsPrefix_pure _ _ _
  | some e => simpa using receive_gro g e

def forgetPoll (s : Nat × Gro × Bool) : Nat × TaggedGro × Bool :=
  (s.1, s.2.1.forget, s.2.2)

theorem poll_gro (pid : PeerId) (budget : Nat) :
    ProjectsPrefix groEvent id (poll pid budget) (rxPollGro pid budget) := by
  unfold poll rxPollGro
  apply projectsPrefix_bind groEvent id id (projectsPrefix_lift _ _)
  intro noBudget
  dsimp only [id]
  apply projectsPrefix_ite
  · intro hb; exact projectsPrefix_pure _ id _
  · intro hb
    apply projectsPrefix_bind groEvent forgetPoll id
    · apply projectsPrefix_range groEvent forgetPoll
      intro n acc
      repeat' first
        | with_reducible exact access_gro (peekAccess_erases _)
        | with_reducible exact access_gro (readyAccess_erases _)
        | with_reducible exact capture_gro _
        | with_reducible exact drop_gro _ _ _ _
        | with_reducible exact receiptObserved_projects (fun _ => rfl) (access_gro (counterValidatePrefix_erases _ _))
        | with_reducible exact receiptObserved_projects (fun _ => rfl) (projectsPrefix_lift _ _)
        | with_reducible exact access_gro (counterValidatePrefix_erases _ _)
        | with_reducible exact access_gro (keypairPutPrefix_erases _ _)
        | with_reducible exact access_gro (peerPutMixed_erases _)
        | with_reducible exact access_gro (freeRxSkbPrefix_erases _)
        | with_reducible exact consume_gro _ _ _ _ _ _
        | with_reducible exact receive_gro _ _
        | with_reducible exact receiveOption_gro _ _
        | with_reducible exact projectsPrefix_lift _ _
        | with_reducible apply projectsPrefix_forIn_map groEvent Gro.forget Entry.tag
        | with_reducible apply projectsPrefix_bind groEvent Gro.forget
        | with_reducible apply projectsPrefix_bind groEvent (Option.map Entry.tag)
        | with_reducible apply projectsPrefix_bind groEvent Prod.fst
        | with_reducible apply projectsPrefix_bind groEvent id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id, forgetPoll]; try simp only [Option.toList_map])
        | (with_reducible split)
        | (simpa [forgetPoll, projectStep, List.map_append, Option.toList_map] using
            projectsPrefix_pure groEvent (projectStep forgetPoll) _)
        | with_reducible exact projectsPrefix_pure groEvent (projectStep Gro.forget) _
      all_goals simp_all [ProjectsPrefix, projectStep, forgetPoll, List.map_append, Option.toList_map, Except.map]
      all_goals exact receiveOption_gro _ _
    · intro acc
      dsimp only [forgetPoll]
      repeat' first
        | with_reducible exact access_gro (completeAccess_erases _)
        | with_reducible exact flushAll_gro _
        | with_reducible exact projectsPrefix_lift _ _
        | with_reducible exact projectsPrefix_pure groEvent id _
        | with_reducible apply projectsPrefix_bind groEvent id
        | with_reducible apply projectsPrefix_ite
        | (with_reducible intro x; try dsimp only [id])
        | (with_reducible split)
      all_goals simp_all [ProjectsPrefix, Except.map]

/-- Exact original result and World or Stop, on every input and history. -/
theorem poll_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (poll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  intro w h
  have hp := congrArg Prod.fst (poll_gro pid budget w h)
  have he := rxPollGro_erases pid budget w (h.filterMap groEvent)
  rw [he] at hp
  cases hr : (runPrefix (poll pid budget) w h).1 <;>
    simpa only [hr, Except.map, id] using hp.symm

theorem peekAccess_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (peekAccess pid) := by
  unfold peekAccess
  repeat' first
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (prevQueuePeek_sameKernel _))
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)

theorem readyAccess_allocation (first : Option SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (readyAccess first) := by
  unfold readyAccess
  apply andPrefix_preserves (fun _ _ hi => hi.safe)
  · exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
  · cases first with
    | none => exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | some skb =>
      exact PrefixPreserves.bind (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _))
        (fun _ => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _))

theorem completeAccess_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (completeAccess pid) :=
  AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ (fun _ => rfl))

theorem capture_access (skb : SkbId) :
    ProjectsPrefix accessEvent Prod.fst (capture skb) (getRxSkbPrefix skb) := by
  intro w h
  rw [capture_run, getRxSkbPrefix_run]
  cases (getRxSkb skb).run w <;> simp [accessEvent, List.filterMap_append, Except.map]

theorem drop_access (pid occurrence skb : Nat) (stamp : PacketStamp) :
    ProjectsUnder AllocationInv accessEvent (drop pid occurrence skb stamp) (rxDropPeekedPrefix pid) := by
  intro w h hi
  have hp := access_projects (rxDropPeekedPrefix_preserves allocationAmbient pid) w h hi
  simp only [drop, runPrefix_bind]
  rw [hp]
  cases hr : runPrefix (access (rxDropPeekedPrefix pid)) w h with
  | mk result hist =>
    cases result <;> simp [runPrefix_emit, accessEvent, List.filterMap_append]

theorem consume_access (pid occurrence skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    ProjectsUnderTo AllocationInv accessEvent (Option.map (fun e : Entry => e.tag.bytes))
      (consume pid occurrence skb stamp pkt ep) (consumeDataDonePrefix pid pkt ep) := by
  intro w h hi
  have hp := access_projects
    (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx pid pkt ep) w h hi
  rw [hp, consume_run]
  cases hr : runPrefix (access (consumeDataDonePrefix pid pkt ep)) w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨out, v⟩
      cases out <;> simp only [map_eq_pure_bind, runPrefix_bind, runPrefix_emit, runPrefix_pure, accessEvent,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil,
        Option.map, Except.map, Prod.fst, Prod.snd]

def erasePoll (s : Nat × Gro × Bool) : Nat × GroState × Bool :=
  (s.1, s.2.1.erase, s.2.2)

theorem receiveOption_access (g : Gro) (out : Option Entry) :
    ProjectsUnderTo AllocationInv accessEvent Gro.erase (out.elim (pure g) (receive g))
      ((out.toList.map fun e => e.tag.bytes).foldlM
        (fun g bytes => napiGroReceivePrefix stackFlushPrefix g bytes) g.erase) := by
  cases out with
  | none => exact projectsUnderTo_pure _ _ _
  | some e => simpa using receive_access g e

macro "rx_joint_allocation" : tactic => `(tactic|
  (change PrefixPreserves AllocationInv LifetimeEvent.Safe _
   repeat' first
    | with_reducible exact peekAccess_allocation _
    | with_reducible exact readyAccess_allocation _
    | with_reducible exact completeAccess_allocation _
    | with_reducible exact rxDropPeekedPrefix_preserves allocationAmbient _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _)
    | with_reducible exact consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx _ _ _
    | with_reducible exact allocationTx.put _ _
    | with_reducible exact allocationAmbient.peerPut _
    | with_reducible exact allocationRx.free _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.kernel (fun _ => True) _ (endpointFromSkb_sameKernel _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.unsupported (fun _ => True) _)
    | with_reducible exact napiGroReceivePrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _ _
    | with_reducible exact napiGroFlushAllPrefix_preserves stackFlushPrefix (fun _ _ hi => hi.safe) stackFlush_allocation _
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.ite
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only [id])
    | (with_reducible split)))

/-- Exact access-history projection, including failed prefixes. The premise
is the existing allocation invariant, not queue ownership or successful drain. -/
theorem poll_access (pid : PeerId) (budget : Nat) :
    ProjectsUnder AllocationInv accessEvent (poll pid budget) (rxPollStackPrefix pid budget) := by
  rw [← pollAccess_eq]
  apply ProjectsUnderTo.identity
  unfold poll pollAccess
  apply projectsUnderTo_bind accessEvent id id (projectsPrefix_lift _ _).underTo
  · rx_joint_allocation
  · intro noBudget
    dsimp only [id]
    apply projectsUnderTo_ite
    · intro hb; exact projectsUnderTo_pure _ id _
    · intro hb
      apply projectsUnderTo_bind accessEvent erasePoll id
      · apply projectsUnderTo_range accessEvent erasePoll
        · intro n acc; rx_joint_allocation
        · intro n acc
          repeat' first
            | with_reducible exact (access_projects (peekAccess_allocation _)).to_mapped
            | with_reducible exact (access_projects (readyAccess_allocation _)).to_mapped
            | with_reducible exact (capture_access _).underTo
            | with_reducible exact (drop_access _ _ _ _).to_mapped
            | with_reducible exact (receiptObserved_projectsUnder (fun _ => rfl) (access_projects (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _)))).to_mapped
            | with_reducible exact (receiptObserved_projects (fun _ => rfl) (projectsPrefix_lift _ _)).underTo
            | with_reducible exact (access_projects (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _))).to_mapped
            | with_reducible exact (access_projects (allocationTx.put _ _)).to_mapped
            | with_reducible exact (access_projects (allocationAmbient.peerPut _)).to_mapped
            | with_reducible exact (access_projects (allocationRx.free _)).to_mapped
            | with_reducible exact consume_access _ _ _ _ _ _
            | with_reducible exact receive_access _ _
            | with_reducible exact receiveOption_access _ _
            | exact projectsUnderTo_lift _ _
            | (solve | rx_joint_allocation)
            | (simp only [Option.toList_map]; apply projectsUnderTo_forIn_map accessEvent Gro.erase (fun e : Entry => e.tag.bytes))
            | with_reducible apply projectsUnderTo_forIn_map accessEvent Gro.erase (fun e : Entry => e.tag.bytes)
            | with_reducible apply projectsUnderTo_bind accessEvent Gro.erase
            | with_reducible apply projectsUnderTo_bind accessEvent (Option.map (fun e : Entry => e.tag.bytes))
            | with_reducible apply projectsUnderTo_bind accessEvent Prod.fst
            | with_reducible apply projectsUnderTo_bind accessEvent id
            | with_reducible apply projectsUnderTo_ite
            | (with_reducible intro x; try dsimp only [id, erasePoll]; try simp only [Option.toList_map])
            | (with_reducible split)
            | (simpa [erasePoll, projectStep, List.map_append, Option.toList_map] using
                projectsUnderTo_pure accessEvent (projectStep erasePoll) _)
            | with_reducible exact projectsUnderTo_pure accessEvent (projectStep Gro.erase) _
          all_goals first | exact projectsUnderTo_lift _ _ | exact receiveOption_access _ _ | rx_joint_allocation
      · rx_joint_allocation
      · intro acc
        dsimp only [erasePoll]
        repeat' first
          | with_reducible exact (access_projects (completeAccess_allocation _)).to_mapped
          | with_reducible exact (flushAll_access _).to_mapped
          | exact projectsUnderTo_lift _ _
          | exact projectsUnderTo_pure accessEvent id _
          | (solve | rx_joint_allocation)
          | with_reducible apply projectsUnderTo_bind accessEvent id
          | with_reducible apply projectsUnderTo_ite
          | (with_reducible intro x; try dsimp only [id])
          | (with_reducible split)
        all_goals exact projectsUnderTo_pure accessEvent id _

end Leanux.Proofs.WG.Queues.RxJoint
