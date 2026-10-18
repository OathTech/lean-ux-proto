import Lean
import Leanux.Proofs.WG.Queues.RxPollJoint

/-! Direct projections of one stamped poll execution. The GRO projection is
unconditional. Access projection uses the existing allocation invariant at
entry and transports it through the exact lower observer. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem peekAccess_erases (pid : PeerId) : ErasesStatePrefix (peekAccess pid) (peekRxQueue pid) := by
  unfold peekAccess peekRxQueue modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem readyAccess_erases (first : Option SkbId) :
    ErasesStatePrefix (readyAccess first) (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  unfold readyAccess
  apply andPrefix_erases_state (erasesStatePrefix_lift _)
  cases first <;> dsimp only
  · exact erasesStatePrefix_lift _
  · exact erasesStatePrefix_bind (getRxSkbPrefix_erases _) (fun _ => erasesStatePrefix_lift _)

theorem completeAccess_erases (pid : PeerId) :
    ErasesStatePrefix (completeAccess pid) (completeRxQueue pid) := by
  unfold completeAccess completeRxQueue modifyPeerKeysPrefix
  exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ => setPeerMixed_erases _ _)

/-- The one original successful getter supplies both the packet and its stamp.
A failed getter contributes no read or capture. -/
theorem capture_run (id : SkbId) (w : World) (h : List Event) :
    runPrefix (capture id) w h = match (liftWG (getRxSkb id)).run w with
    | .error e => (.error e, h)
    | .ok (p, v) => (.ok ((p, packetStamp w.wg id), v),
        h ++ [.access (.packet (.read (.inr id) (packetStamp w.wg id)))]) := by
  have hg (hist : List LifetimeEvent) :
      runPrefix (liftWGObserver (getRxSkbPrefix id)) w hist =
        match (liftWG (getRxSkb id)).run w with
        | .error e => (.error e, hist)
        | .ok (p, v) => (.ok (p, v),
            hist ++ [.packet (.read (.inr id) (packetStamp w.wg id))]) := by
    rw [liftWGObserver_run, liftWG_run]
    change ((runStatePrefix (getRxSkbPrefix id) w.wg w.ambient hist).1.map _,
      (runStatePrefix (getRxSkbPrefix id) w.wg w.ambient hist).2) = _
    rw [getRxSkbPrefix_run]
    cases ((getRxSkb id).run w.wg).run w.ambient <;> rfl
  have hr : runPrefix (access (liftWGObserver (getRxSkbPrefix id))) w h =
      match (liftWG (getRxSkb id)).run w with
      | .error e => (.error e, h)
      | .ok (p, v) => (.ok (p, v), h ++ [.access (.packet (.read (.inr id) (packetStamp w.wg id)))]) := by
    unfold access
    cases he : (liftWG (getRxSkb id)).run w with
    | error e =>
      simpa only [List.map_nil, List.append_nil] using
        focusPrefix_suffix Event.access accessEvent (liftWGObserver (getRxSkbPrefix id)) w h (.error e) []
          (by rw [hg, he]; simp only [List.append_nil])
    | ok out => exact focusPrefix_suffix _ _ _ _ _ _ _ (by rw [hg, he])
  change ((runPrefix (access (liftWGObserver (getRxSkbPrefix id))) w h).1.map _,
    (runPrefix (access (liftWGObserver (getRxSkbPrefix id))) w h).2) = _
  rw [hr]
  cases (liftWG (getRxSkb id)).run w <;> rfl

theorem capture_gro (id : SkbId) :
    ProjectsPrefix groEvent Prod.fst (capture id) (liftPrefix (liftWG (getRxSkb id))) := by
  intro w h
  rw [capture_run, runPrefix_lift]
  cases (liftWG (getRxSkb id)).run w <;> simp [groEvent, List.filterMap_append, Except.map]

theorem drop_gro (pid occurrence skb : Nat) (stamp : PacketStamp) :
    ProjectsPrefix groEvent id (drop pid occurrence skb stamp) (dropGroPrefix pid occurrence skb) := by
  unfold drop dropGroPrefix
  exact projectsPrefix_bind groEvent id id (access_gro (liftWGObserver_erases (rxDropPeekedPrefix_erases _)))
    (fun _ => projectsPrefix_emit _ _)

theorem consume_gro (pid occurrence skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    ProjectsPrefix groEvent (Option.map Entry.tag) (consume pid occurrence skb stamp pkt ep)
      (consumeGro pid occurrence skb pkt ep) := by
  intro w h
  have hp := access_gro (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h
  simp only [consumeGro, runPrefix_bind]
  rw [hp, consume_run]
  cases runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨out, v⟩
      cases out <;> simp only [runPrefix_bind, runPrefix_emit, runPrefix_pure, groEvent,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil,
        Option.map, Except.map, id]

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
        | with_reducible exact access_gro (liftWGObserver_erases (peekAccess_erases _))
        | with_reducible exact access_gro (liftWGObserver_erases (readyAccess_erases _))
        | with_reducible exact capture_gro _
        | with_reducible exact drop_gro _ _ _ _
        | with_reducible exact receiptObserved_projects (fun _ => rfl) (access_gro (liftWGObserver_erases (counterValidatePrefix_erases _ _)))
        | with_reducible exact receiptObserved_projects (fun _ => rfl) (projectsPrefix_lift _ _)
        | with_reducible exact access_gro (liftWGObserver_erases (counterValidatePrefix_erases _ _))
        | with_reducible exact access_gro (liftWGObserver_erases (keypairPutPrefix_erases _ _))
        | with_reducible exact access_gro (liftWGObserver_erases (peerPutMixed_erases _))
        | with_reducible exact access_gro (liftWGObserver_erases (freeRxSkbPrefix_erases _))
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
      all_goals simp_all [ProjectsPrefix, Option.toList_map, Except.map]
      all_goals try (intro w; cases ((branch .rxPollBudgetDone (decide (budget ≤ acc.1 + 1)) : Leanux.M Bool).run w) <;> rfl)
      all_goals exact receiveOption_gro _ _
    · intro acc
      dsimp only [forgetPoll]
      repeat' first
        | with_reducible exact access_gro (liftWGObserver_erases (completeAccess_erases _))
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
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (peekAccess pid) := by
  unfold peekAccess
  repeat' first
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.store (fun _ => True) _ (prevQueuePeek_sameWGStore _))
    | with_reducible exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)

theorem readyAccess_allocation (first : Option SkbId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (readyAccess first) := by
  unfold readyAccess
  apply andPrefix_preserves_state (fun _ _ _ hi => hi.safe)
  · exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
  · cases first with
    | none => exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | some skb =>
      exact StatePrefixEnsures.bind (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _))
        (fun _ => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _))

theorem completeAccess_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (completeAccess pid) :=
  AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient allocationAmbient (fun _ => True) _ _ (fun _ => rfl))

theorem capture_access (skb : SkbId) :
    ProjectsPrefix accessEvent Prod.fst (capture skb) (liftWGObserver (getRxSkbPrefix skb)) := by
  intro w h
  rw [capture_run, liftWGObserver_run, liftWG_run]
  change ((runStatePrefix (getRxSkbPrefix skb) w.wg w.ambient (h.filterMap accessEvent)).1.map _,
    (runStatePrefix (getRxSkbPrefix skb) w.wg w.ambient (h.filterMap accessEvent)).2) = _
  rw [getRxSkbPrefix_run]
  cases ((getRxSkb skb).run w.wg).run w.ambient <;>
    simp [accessEvent, List.filterMap_append, Except.map]

theorem drop_access (pid occurrence skb : Nat) (stamp : PacketStamp) :
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) accessEvent (drop pid occurrence skb stamp) (liftWGObserver (rxDropPeekedPrefix pid)) := by
  intro w h hi
  have hp := access_projects ((rxDropPeekedPrefix_preserves allocationAmbient pid).liftWGObserver) w h hi
  simp only [drop, runPrefix_bind]
  rw [hp]
  cases hr : runPrefix (access (liftWGObserver (rxDropPeekedPrefix pid))) w h with
  | mk result hist =>
    cases result <;> simp [runPrefix_emit, accessEvent, List.filterMap_append]

theorem consume_access (pid occurrence skb : Nat) (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    ProjectsUnderTo (fun h (w : World) => AllocationInv h w.wg) accessEvent (Option.map (fun e : Entry => e.tag.bytes))
      (consume pid occurrence skb stamp pkt ep) (liftWGObserver (consumeDataDonePrefix pid pkt ep)) := by
  intro w h hi
  have hp := access_projects
    (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx pid pkt ep).liftWGObserver w h hi
  rw [hp, consume_run]
  cases hr : runPrefix (access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result hist =>
    cases result with
    | error e => rfl
    | ok out =>
      rcases out with ⟨out, v⟩
      cases out <;> simp only [accessEvent, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.append_nil, Option.map, Except.map]

def erasePoll (s : Nat × Gro × Bool) : Nat × GroState × Bool :=
  (s.1, s.2.1.erase, s.2.2)

theorem receiveOption_access (g : Gro) (out : Option Entry) :
    ProjectsUnderTo (fun h (w : World) => AllocationInv h w.wg) accessEvent Gro.erase (out.elim (pure g) (receive g))
      ((out.toList.map fun e => e.tag.bytes).foldlM
        (fun g bytes => napiGroReceivePrefix stackFlushPrefix g bytes) g.erase) := by
  cases out with
  | none => exact projectsUnderTo_pure _ _ _
  | some e => simpa using receive_access g e

elab "rx_joint_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "not an observer contract"
  let mut action := (if ty.isAppOf ``PrefixPreserves then args.back! else args[args.size - 2]!).consumeMData
  let expected := name.getId.eraseMacroScopes.toString
  for wrapper in [``access, ``liftWGObserver, ``liftPrefix, ``liftWGPrefix,
      ``liftM, ``MonadLiftT.monadLift, ``MonadLift.monadLift, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString &&
        !wrapper.toString.endsWith ("." ++ expected) then
      unless action.getAppArgs.size > 0 do Lean.throwError "missing lifted observer"
      action := action.getAppArgs.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant-headed observer"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different observer head"

macro "rx_joint_allocation" : tactic => `(tactic|
  (change PrefixPreserves (fun h (w : World) => AllocationInv h w.wg) LifetimeEvent.Safe _
   repeat' first
    | (rx_joint_head peekAccess; exact (peekAccess_allocation _).liftWGObserver)
    | (rx_joint_head readyAccess; exact (readyAccess_allocation _).liftWGObserver)
    | (rx_joint_head completeAccess; exact (completeAccess_allocation _).liftWGObserver)
    | (rx_joint_head rxDropPeekedPrefix; exact (rxDropPeekedPrefix_preserves allocationAmbient _).liftWGObserver)
    | (rx_joint_head getRxSkbPrefix; exact (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _)).liftWGObserver)
    | (rx_joint_head counterValidatePrefix; exact (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _)).liftWGObserver)
    | (rx_joint_head consumeDataDonePrefix; exact (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx _ _ _).liftWGObserver)
    | (rx_joint_head keypairPutPrefix; exact (allocationTx.put _ _).liftWGObserver)
    | (rx_joint_head peerPutMixed; exact (allocationAmbient.peerPut _).liftWGObserver)
    | (rx_joint_head freeRxSkbPrefix; exact (allocationRx.free _).liftWGObserver)
    | (rx_joint_head endpointFromSkb; exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).nativeStore (fun _ => True) _ (endpointFromSkb_sameWGStore _)))
    | (rx_joint_head branch; exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).branch (fun _ => True) _ _))
    | (rx_joint_head invariant; exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).invariant (fun _ => True) _))
    | (rx_joint_head unsupported; exact ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).ambient (fun _ => True) (AmbientM.unsupported _)))
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
    ProjectsUnder (fun h (w : World) => AllocationInv h w.wg) accessEvent (poll pid budget) (rxPollStackPrefix pid budget) := by
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
            | (rx_joint_head peekAccess; exact (access_projects ((peekAccess_allocation _).liftWGObserver)).to_mapped)
            | (rx_joint_head readyAccess; exact (access_projects ((readyAccess_allocation _).liftWGObserver)).to_mapped)
            | with_reducible exact (capture_access _).underTo
            | with_reducible exact (drop_access _ _ _ _).to_mapped
            | (rx_joint_head receiptObserved; exact (receiptObserved_projectsUnder (fun _ => rfl) (access_projects ((AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _)).liftWGObserver))).to_mapped)
            | with_reducible exact (receiptObserved_projects (fun _ => rfl) (projectsPrefix_lift _ _)).underTo
            | (rx_joint_head counterValidatePrefix; exact (access_projects ((AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) _ _)).liftWGObserver)).to_mapped)
            | (rx_joint_head keypairPutPrefix; exact (access_projects ((allocationTx.put _ _).liftWGObserver)).to_mapped)
            | (rx_joint_head peerPutMixed; exact (access_projects ((allocationAmbient.peerPut _).liftWGObserver)).to_mapped)
            | (rx_joint_head freeRxSkbPrefix; exact (access_projects ((allocationRx.free _).liftWGObserver)).to_mapped)
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
            | (rx_joint_head Pure.pure; exact projectsUnderTo_pure accessEvent (projectStep Gro.erase) _)
          all_goals first | exact projectsUnderTo_lift _ _ | exact receiveOption_access _ _ | rx_joint_allocation
      · rx_joint_allocation
      · intro acc
        dsimp only [erasePoll]
        repeat' first
          | (rx_joint_head completeAccess; exact (access_projects ((completeAccess_allocation _).liftWGObserver)).to_mapped)
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
