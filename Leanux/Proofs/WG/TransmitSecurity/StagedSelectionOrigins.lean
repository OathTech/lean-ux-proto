import Leanux.Proofs.WG.TransmitSecurity.StagedSelectionFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedOriginHistory

/-! A selected saved batch retains its original source tickets while its native
peer queue is empty. Selection itself creates no plaintext occurrence. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Saved (history : List Event) (pid : PeerId) (peer : Peer) (w : WGWorld) : Prop :=
  ∃ generation, Packets.epoch w = some generation ∧
    stagedAt w pid = some (peer.internalId,[]) ∧
    Batch history generation pid peer.internalId peer.staged

theorem Saved.append (saved : Saved h pid peer w) (suffix : List Event) : Saved (h ++ suffix) pid peer w := by
  obtain ⟨generation,epoch,empty,batch⟩ := saved
  exact ⟨generation,epoch,empty,batch.append_history suffix⟩

theorem selection_origin (pid : PeerId) (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (HandshakeSecurity.Responder.selectionPrefix pid))
    (before : Inv history r.before) :
    Inv history r.after ∧ Checked history (.old (.responder (.selected pid r))) ∧
      (∀ peer key, r.value = some (peer,key) → Saved history pid peer r.after) := by
  have run := valid
  unfold WGRunWitness.Valid HandshakeSecurity.Responder.selectionPrefix at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,a,read,tail⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ :=
    Leanux.Proofs.WG.Origins.getPeer_return pid r.before u p r.ambientBefore a read
  subst u
  subst a
  rw [MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨empty,u,a,test,tail⟩ := tail
  have actual : ((branch .stagedEmpty p.staged.isEmpty : WG.M Bool).run r.before).run
      r.ambientBefore = .ok ((p.staged.isEmpty,r.before),
        CounterWindow.record r.ambientBefore .stagedEmpty p.staged.isEmpty) := rfl
  rw [actual] at test
  cases test
  cases empty : p.staged.isEmpty with
  | true =>
    simp only [empty,ite_true,StateT.run_pure,CounterWindow.except_pure,
      Except.ok.injEq,Prod.mk.injEq] at tail
    obtain ⟨⟨value,world⟩,_⟩ := tail
    refine ⟨world ▸ before,?_,?_⟩
    · intro peer key selected
      rw [← value] at selected
      cases selected
    · intro peer key selected
      rw [← value] at selected
      cases selected
  | false =>
    simp only [empty,Bool.false_eq_true,ite_false] at tail
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ignored,u,a,clear,tail⟩ := tail
    cases ignored
    have cleared : u = {r.before with dev := r.before.dev.map fun d =>
        {d with peers := d.peers.insert pid {p with staged := []}}} :=
      (congrArg (fun out => out.1.2) (Except.ok.inj clear)).symm
    have held : Inv history u := cleared ▸ before.clear pid p
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨key,v,b,borrowed,returned⟩ := tail
    simp only [StateT.run_pure,CounterWindow.except_pure,Except.ok.injEq,Prod.mk.injEq] at returned
    obtain ⟨⟨value,world⟩,_⟩ := returned
    have kept : Inv history r.after := world ▸
      (hoare_iff_run_ambient _ _ _).mp (Native.key_get p.keypairCurrent) u a key v b held borrowed
    have sameEpoch := (ProjectedAction.iff_run_ambient _ _ _).mp
      (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire p.keypairCurrent).factor Prod.fst))
      u a key v b borrowed
    have sameQueue := (ProjectedAction.iff_run_ambient _ _ _).mp
      (key_get_staged p.keypairCurrent) u a key v b borrowed
    have originalEpoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
    have batch : Batch history d.ifindex pid p.internalId p.staged :=
      before d.ifindex originalEpoch pid p.internalId p.staged (by simp [stagedAt,device,resident])
    have checked : Checked history (.old (.responder (.selected pid r))) := by
      intro peer slot selected
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (value.trans selected))
      exact ⟨d.ifindex,originalEpoch,batch⟩
    refine ⟨kept,checked,?_⟩
    intro peer slot selected
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (value.trans selected))
    refine ⟨d.ifindex,?_,?_,batch⟩
    · rw [← world]
      change PacketOrigins.epoch v = some d.ifindex
      rw [sameEpoch]
      simp [PacketOrigins.epoch,cleared,device]
    · rw [← world,sameQueue]
      simp [stagedAt,cleared,device]

theorem selection_observed (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (state (Journal.selection pid))
      (fun value h w _ => Carrier h w ∧ ∀ peer key, value = some (peer,key) → Saved h pid peer w) := by
  unfold state Journal.selection HandshakeSecurity.Responder.DriverCuts.selection
  rw [focused_native_receipt,focused_native_receipt]
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
    obtain ⟨inv,checked,saved⟩ := selection_origin pid receipt run before.1
    have safe := before.2.emit checked
    exact ⟨[.old (.responder (.selected pid receipt))],rfl,safe,
      ⟨inv.append _,safe⟩,fun peer key selected => (saved peer key selected).append _⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
