import Leanux.Proofs.WG.RetirementSecurity.HandshakeSendDispatch

/-! Slot anchors survive actual work callbacks even when the callback pays a
peer reference or clears a key slot. The base/caller owner list stays separate
from the work occurrence being paid. No distinct-slot premise is needed. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def HasKeySlot (p : Peer) : Prop :=
  p.keypairNext ≠ none ∨ p.keypairPrevious ≠ none ∨ p.keypairCurrent ≠ none

theorem SlotPeerReferences.rename (before : SlotPeerReferences holders loans w)
    (owners : holders.base ++ loans = next.base ++ extra) : SlotPeerReferences next extra w := by
  intro d pid p device stored slots
  rw [← owners]
  exact before d pid p device stored slots

theorem SlotPeerReferences.replace (before : SlotPeerReferences holders loans w)
    (device : w.dev = some d) (stored : d.peers[pid]? = some p)
    (stamp : q.internalId = p.internalId) (slots : HasKeySlot q → HasKeySlot p) :
    SlotPeerReferences holders loans (replacePeer w d pid q) := by
  intro after other current found resident present
  simp only [replacePeer,Option.some.injEq] at found
  subst after
  by_cases same : pid = other
  · subst other
    simp only [Std.TreeMap.getElem?_insert_self,Option.some.injEq] at resident
    subst current
    simpa only [stamp] using before d pid p device stored (slots present)
  · exact before d other current device
      (by simpa [Std.TreeMap.getElem?_insert,same] using resident) present

namespace SlotAnchors

theorem frame {action : WG.M α} (peers : SameView peerView action)
    (points : SameView ownershipPointView action) :
    Preserves (SlotPeerReferences holders loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.transport
    ((ProjectedAction.iff_run_ambient _ _ _).mp peers w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp points w a result v b run)
    (List.Perm.refl _)

theorem update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p, (f p).internalId = p.internalId)
    (slots : ∀ p, HasKeySlot (f p) → HasKeySlot p) :
    Preserves (SlotPeerReferences holders loans)
      (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,read,c,getter,setter⟩ := run
  obtain ⟨world,ambient,d,device,stored⟩ := getPeer_normal pid w read p a c getter
  subst read
  subst c
  have final : (((),replacePeer w d pid (f p)),a) = ((result,v),b) := by
    simpa [setPeer,modifyDev,replacePeer,device] using setter
  cases final
  exact before.replace device stored (stamp p) (slots p)

theorem modify (f : Device → Device) (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (peers : ∀ d, (f d).peers = d.peers) :
    Preserves (SlotPeerReferences holders loans) (modifyDev f) := by
  unfold modifyDev
  apply hoare_modify
  intro w before d pid p device stored slots
  cases oldDevice : w.dev with
  | none => simp [oldDevice] at device
  | some old =>
    simp only [oldDevice,Option.map_some,Option.some.injEq] at device
    subst d
    simpa only [epoch] using before old pid p oldDevice (by simpa only [peers] using stored) slots

theorem key_put (id : Option KeypairId) (now : Bool) :
    Preserves (SlotPeerReferences holders loans) (keypairPut id now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  have peers := put_peers id now w v a b run
  have credit := (ProjectedAction.iff_run_ambient _ _ _).mp
    (keypairPut_credit_frame id now) w a () v b run
  intro d pid p device stored slots
  cases oldDevice : w.dev with
  | none => simp [peersAt,device,oldDevice] at peers
  | some old =>
    have maps : d.peers = old.peers := by
      simpa only [peersAt,device,oldDevice,Option.map_some,Option.some.injEq] using peers
    have epoch : d.ifindex = old.ifindex := by
      have same := congrArg (fun s => s.1.1) credit
      simpa only [peerView,device,oldDevice,Option.map_some,Option.some.injEq] using same
    simpa only [epoch] using before old pid p oldDevice (maps ▸ stored) slots

/-- A native final peer payment may remove a peer. Every surviving published
slot keeps the same stamped base/caller anchor, including on a nonfinal put. -/
theorem peer_put (word : Option PeerId) :
    Preserves (SlotPeerReferences holders loans) (peerPut word) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  cases word with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact before
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
          invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lift,liftIndex_run,retirePeerUnits,modifyAmbient,
              CounterWindow.branch_run,CounterWindow.branchCmp_run,
              device,stored,positive,nonzero,final,
              StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
              CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals intro after other current found resident slots
          all_goals cases found
          all_goals by_cases same : pid = other
          all_goals simp [Std.TreeMap.getElem?_insert,Std.TreeMap.getElem?_erase,same] at resident
          all_goals first
            | (subst other; subst current; exact before d pid p device stored slots)
            | exact before d other current device resident slots
        · have zero : p.refcount = 0 := by omega
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,zero,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at run
          cases run

theorem clear (pid : PeerId) : Preserves (SlotPeerReferences holders loans) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update pid (fun p => {p with keypairNext := none}) (fun _ => rfl) (by
    intro p h
    simp only [HasKeySlot] at h ⊢
    rcases h with h | h | h <;> simp_all))
  intro _
  apply preserves_bind (key_put p.keypairNext true)
  intro _
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update pid (fun p => {p with keypairPrevious := none}) (fun _ => rfl) (by
    intro p h
    simp only [HasKeySlot] at h ⊢
    rcases h with h | h | h <;> simp_all))
  intro _
  apply preserves_bind (key_put p.keypairPrevious true)
  intro _
  apply preserves_bind (getPeer_preserves pid _)
  intro p
  apply preserves_bind (update pid (fun p => {p with keypairCurrent := none}) (fun _ => rfl) (by
    intro p h
    simp only [HasKeySlot] at h ⊢
    rcases h with h | h | h <;> simp_all))
  intro _
  exact key_put p.keypairCurrent true

end SlotAnchors
end Leanux.Proofs.WG.RetirementSecurity
