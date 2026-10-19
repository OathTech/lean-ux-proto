import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableNative
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityBirth

/-! Actual native routing fronts extend the available-birth carrier at their
completed splice. Error returns add no staged births; overflow keeps its
already certified suffix. The later send may still stop. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem routing_success (receipt : Journal.RoutingHistory.Receipt)
    (valid : receipt.Valid) (pid : PeerId) (selected : receipt.run.value = .ok pid)
    (before : Inv history receipt.run.before) :
    Inv (history ++ [.old (.routed receipt.family receipt.addr receipt.packets receipt.mtu receipt.run)])
      receipt.run.after := by
  obtain ⟨cut,_⟩ := receipt.selection valid pid selected
  obtain ⟨u,q,r,a,b,c,check,lookup,select,spliceRun⟩ := cut
  have atCheck := (hoare_iff_run_ambient _ _ _).mp
    (Native.check receipt.family receipt.addr receipt.packets receipt.mtu)
    receipt.run.before receipt.run.ambientBefore true u a before check
  have atLookup := (hoare_iff_run_ambient _ _ _).mp
    (Native.lookup receipt.family receipt.addr) u a (some pid) q b atCheck lookup
  have atSplice := (hoare_iff_run_ambient _ _ _).mp
    (Native.select receipt.family receipt.packets receipt.mtu (some pid))
    q b _ r c atLookup select
  let packets := receipt.packets.map (fun p => {p with mtu := receipt.mtu})
  let spliced : WGRunWitness Unit := ⟨(),r,receipt.run.after,c,receipt.run.ambientAfter⟩
  have native : spliced.Valid (xmitSplice pid packets) := spliceRun
  obtain ⟨d,p,device,resident,after,_⟩ := splice pid packets spliced native
  dsimp only [spliced] at device after
  have epoch : Packets.epoch receipt.run.after = some d.ifindex := by
    simp only [Packets.epoch,after,Option.map_some]
  have sameEpoch : Packets.epoch receipt.run.after = Packets.epoch r := by
    simp only [Packets.epoch,after,device,Option.map_some]
  have slot : stagedAt receipt.run.after pid = some (p.internalId,p.staged ++ packets) := by
    simp only [stagedAt,after,Option.bind_some,Std.TreeMap.getElem?_insert_self,Option.map_some]
  have batch := atSplice d.ifindex (by simp only [Packets.epoch,device,Option.map_some])
    pid p.internalId p.staged (by simp only [stagedAt,device,Option.bind_some,resident,Option.map_some])
  apply atSplice.changed [_] (fun _ => by simp [Quiet,Uses]) sameEpoch epoch slot
  · intro q different
    simp only [stagedAt,after,device,Option.bind_some,Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq,Ne.symm different,↓reduceIte]
  · exact batch.append_births (by simp [Quiet,Uses])
      (Origins.routed_births receipt valid selected epoch slot history)

theorem routing_failure (receipt : Journal.RoutingHistory.Receipt)
    (valid : receipt.Valid) (err : Int) (refused : receipt.run.value = .error err)
    (before : Inv history receipt.run.before) : Inv history receipt.run.after := by
  have run := valid
  unfold Journal.RoutingHistory.Receipt.Valid WGRunWitness.Valid Packets.txFront at run
  rw [refused,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨checked,u,a,check,tail⟩ := run
  have atCheck := (hoare_iff_run_ambient _ _ _).mp
    (Native.check receipt.family receipt.addr receipt.packets receipt.mtu)
    receipt.run.before receipt.run.ambientBefore checked u a before check
  cases checked with
  | false =>
    simp only [Bool.not_false,ite_true,StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at tail
    exact tail.1.2 ▸ atCheck
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨peer,q,b,lookup,tail⟩ := tail
    have atLookup := (hoare_iff_run_ambient _ _ _).mp
      (Native.lookup receipt.family receipt.addr) u a peer q b atCheck lookup
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨selection,r,c,select,tail⟩ := tail
    have atSelect := (hoare_iff_run_ambient _ _ _).mp
      (Native.select receipt.family receipt.packets receipt.mtu peer) q b selection r c atLookup select
    cases selection with
    | error reason =>
      simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at tail
      exact tail.1.2 ▸ atSelect
    | ok pair =>
      obtain ⟨pid,packets⟩ := pair
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨value,v,d,_,tail⟩ := tail
      simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq,
        reduceCtorEq,false_and] at tail

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
