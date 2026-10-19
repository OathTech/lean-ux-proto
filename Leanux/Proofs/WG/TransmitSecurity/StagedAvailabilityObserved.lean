import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilitySelection

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

abbrev StateSafe (action : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Carrier h w) Safe action

theorem state_lift (action : WG.M α) (native : ∀ h, Preserves (Inv h) action) :
    StateSafe (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
    (fun h w a value v b before run =>
      ⟨(hoare_iff_run_ambient _ _ _).mp (native h) w a value v b before.1 run,before.2⟩)

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.2) (fun _ _ _ before => before)

theorem quiet_singleton (quiet : allocation? event = none) (pid : PeerId) : Quiet pid [event] := by
  intro e member
  have same := List.mem_singleton.mp member
  subst e
  exact no_use quiet

theorem state_emit (event : Event) (quiet : allocation? event = none) : StateSafe (emitStatePrefix event) := by
  apply StatePrefixEnsures.emit
  · intro h w a before
    exact before.2.emit (quiet_event quiet)
  · intro h w a before
    exact ⟨before.1.append (quiet_singleton quiet),before.2.emit (quiet_event quiet)⟩

theorem selection_observed (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (state (Journal.selection pid))
      (fun value h w _ => Carrier h w ∧ ∀ peer key, value = some (peer,key) → Saved h pid peer w) := by
  unfold state Journal.selection HandshakeSecurity.Responder.DriverCuts.selection
  rw [Origins.focused_native_receipt,Origins.focused_native_receipt]
  intro w a h before
  have equation := runWGPrefix_receiptWGObserved
    (liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid))
    (Event.old ∘ Journal.Event.responder ∘ HandshakeSecurity.Responder.DriverCuts.Event.selected pid) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((HandshakeSecurity.Responder.selectionPrefix pid).run w).run a with
  | error stop => exact ⟨[],by simp,before.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let receipt : WGRunWitness (Option (Peer × Option KeypairId)) := ⟨value,w,v,a,b⟩
    obtain ⟨inv,saved⟩ := selection_origin pid receipt run before.1
    have safe := before.2.emit (quiet_event (show allocation? (.old (.responder (.selected pid receipt))) = none from rfl))
    exact ⟨[.old (.responder (.selected pid receipt))],rfl,safe,
      ⟨inv.append (quiet_singleton rfl),safe⟩,
      fun peer key selected => (saved peer key selected).append (quiet_singleton rfl pid)⟩

def Held (pid : PeerId) (peer : Peer) (history : List Event) (w : WGWorld) (_ : Ambient) : Prop :=
  Carrier history w ∧ Saved history pid peer w

def Allocating (pid : PeerId) (peer : Peer) (packets : List DataPacket)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Held pid peer history w a ∧ packets.map DataPacket.plaintext = peer.staged ∧
    ∀ packet ∈ packets, packet.peer = pid

theorem allocate_observed (pid : PeerId) (peer : Peer) (packets : List DataPacket) :
    StatePrefixEnsures (Allocating pid peer packets) Safe (state (Journal.allocate packets))
      (fun _ h w _ => Carrier h w) := by
  unfold state Journal.allocate
  rw [Origins.focused_native_receipt]
  intro w a h before
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb))
    (Event.old ∘ Journal.Event.allocated packets) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((packets.mapM newTxSkb).run w).run a with
  | error stop => exact ⟨[],by simp,before.1.1.2,True.intro⟩
  | ok out =>
    obtain ⟨⟨items,v⟩,b⟩ := out
    let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,b⟩
    obtain ⟨generation,epoch,empty,batch⟩ := before.1.2
    have source : Source h packets := Source.of_batch (before.2.1.symm ▸ batch) before.2.2
    have safe := before.1.1.2.emit (show Checked h (.old (.allocated packets receipt)) from ⟨run,source⟩)
    have inv := allocated_inv packets receipt run before.1.1.1 (pid := pid) (by
      intro stamp staged found
      have fields := Prod.mk.inj (Option.some.inj (found.symm.trans empty))
      exact fields.2) before.2.2
    exact ⟨[.old (.allocated packets receipt)],rfl,safe,inv,safe⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
