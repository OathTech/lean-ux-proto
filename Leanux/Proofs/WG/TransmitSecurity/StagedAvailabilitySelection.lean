import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilitySelectionFrames

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem selection_origin (pid : PeerId) (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (HandshakeSecurity.Responder.selectionPrefix pid))
    (before : Inv history r.before) :
    Inv history r.after ∧
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
    refine ⟨world ▸ before,?_⟩
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
      (hoare_iff_run_ambient _ _ _).mp (frame (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire p.keypairCurrent).factor Prod.fst))
        (Staged.key_get p.keypairCurrent)) u a key v b held borrowed
    have sameEpoch := (ProjectedAction.iff_run_ambient _ _ _).mp
      (PacketOrigins.epoch_ring ((RetirementSecurity.keyGet_cryptWire p.keypairCurrent).factor Prod.fst))
      u a key v b borrowed
    have sameQueue := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.key_get_staged p.keypairCurrent) u a key v b borrowed
    have originalEpoch : Packets.epoch r.before = some d.ifindex := by simp [Packets.epoch,device]
    have batch : Batch history d.ifindex pid p.internalId p.staged :=
      before d.ifindex originalEpoch pid p.internalId p.staged (by simp [stagedAt,device,resident])
    refine ⟨kept,?_⟩
    intro peer slot selected
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (value.trans selected))
    refine ⟨d.ifindex,?_,?_,batch⟩
    · rw [← world]
      change PacketOrigins.epoch v = some d.ifindex
      rw [sameEpoch]
      simp [PacketOrigins.epoch,cleared,device]
    · rw [← world,sameQueue]
      simp [stagedAt,cleared,device]


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
