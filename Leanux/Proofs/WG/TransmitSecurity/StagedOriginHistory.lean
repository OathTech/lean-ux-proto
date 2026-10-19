import Leanux.Proofs.WG.TransmitSecurity.StagedKeepaliveOrigins
import Leanux.Proofs.WG.TransmitSecurity.StagedRoutingOrigins

/-! Staged origins use the full causal journal's positions. Focusing an actual
native receipt only tags that new receipt; it does not renumber prior events. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal

theorem focused_native_receipt (encode : E → F) (decode : F → Option E)
    (action : WG.M α) (record : WGRunWitness α → E) :
    focusStatePrefix encode decode (receiptWGObserved (liftWGPrefix action) record) =
      receiptWGObserved (liftWGPrefix action) (encode ∘ record) := by
  funext w a h
  change runWGPrefix (focusStatePrefix encode decode _) w a h = runWGPrefix _ w a h
  have inner := runWGPrefix_receiptWGObserved (liftWGPrefix action) record w a (h.filterMap decode)
  rw [runWGPrefix_lift] at inner
  have outer := runWGPrefix_receiptWGObserved (liftWGPrefix action) (encode ∘ record) w a h
  rw [runWGPrefix_lift] at outer
  apply Eq.trans ?_ outer.symm
  change ((runWGPrefix (receiptWGObserved (liftWGPrefix action) record) w a (h.filterMap decode)).1,
    h ++ ((runWGPrefix (receiptWGObserved (liftWGPrefix action) record) w a (h.filterMap decode)).2.drop
      (h.filterMap decode).length).map encode) = _
  rw [inner]
  cases run : (action.run w).run a with
  | error stop => simp
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    simp

abbrev StateSafe (action : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Carrier h w) Safe action

theorem state_lift (action : WG.M α) (native : ∀ h, Preserves (Inv h) action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
    (fun h w a value v b before run =>
      ⟨(hoare_iff_run_ambient _ _ _).mp (native h) w a value v b before.1 run,before.2⟩)

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.2) (fun _ _ _ before => before)

theorem state_emit (event : Event) (quiet : Quiet event) : StateSafe (emitStatePrefix event) := by
  apply StatePrefixEnsures.emit
  · intro h w a before
    exact before.2.emit (checked_quiet event quiet h)
  · intro h w a before
    exact ⟨before.1.append _,before.2.emit (checked_quiet event quiet h)⟩

theorem routing_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (state (Journal.front family addr packets mtu)) := by
  unfold state Journal.front
  rw [focused_native_receipt]
  intro w a h before
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (Packets.txFront family addr packets mtu))
    (Event.old ∘ Journal.Event.routed family addr packets mtu) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((Packets.txFront family addr packets mtu).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : Journal.RoutingHistory.Receipt := ⟨family,addr,packets,mtu,⟨value,w,v,a,b⟩⟩
    have safe : Safe (h ++ [.old (.routed family addr packets mtu receipt.run)]) := before.2.emit True.intro
    refine ⟨[.old (.routed family addr packets mtu receipt.run)],rfl,safe,?_,safe⟩
    cases value with
    | error err => exact (routing_failure receipt run err rfl before.1).append _
    | ok pid => exact routing_success receipt run pid rfl before.1

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
