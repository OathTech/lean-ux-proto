import Leanux.Proofs.WG.Noise.SessionReadyClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem beginSession_rejected_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (notCreated : p.handshakeState ≠ HANDSHAKE_CREATED_RESPONSE)
    (notConsumed : p.handshakeState ≠ HANDSHAKE_CONSUMED_RESPONSE)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d) :
    ((beginSession pid).run g).run ambient = .ok ((false, g),
      {ambient with steps := (ambient.steps.push {
        decision := .sessionNotCreatedResponse, outcome := true, netRx := ambient.netRxSection}).push {
        decision := .sessionNotConsumedResponse, outcome := true, netRx := ambient.netRxSection}}) := by
  have createdB : (p.handshakeState != HANDSHAKE_CREATED_RESPONSE) = true := by
    simpa only [bne_iff_ne] using notCreated
  have consumedB : (p.handshakeState != HANDSHAKE_CONSUMED_RESPONSE) = true := by
    simpa only [bne_iff_ne] using notConsumed
  rw [Index.beginSession_owner_source]
  simp [getPeer, getDev, device, resident, WG.andM, branch, AmbientM.branch,
    createdB, consumedB, notCreated]
  rfl

theorem sessionAllocation_refused_run (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (refused : bytes.headD 2 = 0)
    (ambient : Ambient)
    (present : ambient.hidden = some ({site := 80, bytes := bytes} :: rest))
    (armed : ambient.allocArmed.contains "kzallocKeypair" = true) :
    (AmbientM.hiddenAlloc .kzallocKeypair).run ambient =
      .ok (false, {ambient with hidden := some rest}) := by
  have record : ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord)
      .kzallocKeypair).run ambient = .ok (false, {ambient with hidden := some rest}) := by
    change ((do
      let bs ← AmbientM.hidden (.alloc .kzallocKeypair)
      match bs.headD 2 with
      | 1 => pure true
      | 0 => pure false
      | b => throw (Stop.hidden s!"kzallocKeypair: outcome byte {b}, expected 0 or 1")).run ambient) = _
    rw [StateT.run_bind, sessionAllocationRecord_run bytes rest width ambient present]
    simp only [bind, Except.bind]
    rw [refused]
    rfl
  rw [sessionAllocation_source]
  simp only [StateT.run_bind, StateT.run_get, present, Option.isNone_some,
    Bool.false_and, Bool.not_false, armed, Bool.not_true, Bool.true_and,
    Bool.false_eq_true, ite_false, pure_bind]
  rw [sessionAllocationLoop_unfold]
  simp only [Nat.zero_lt_one, ite_true, StateT.run_bind, record]
  rfl

theorem beginSession_allocation_refused_run (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (refused : bytes.headD 2 = 0)
    (g : WGWorld) (ambient : Ambient) (device : g.dev = some d)
    (present : ambient.hidden = some ({site := 80, bytes := bytes} :: rest))
    (armed : ambient.allocArmed.contains "kzallocKeypair" = true) :
    ∃ after, ((beginSession pid).run g).run ambient = .ok ((false, g), after) ∧
      after.hidden = some rest := by
  let first := {ambient with steps := ambient.steps.push {
    decision := .sessionNotCreatedResponse, outcome := p.handshakeState != HANDSHAKE_CREATED_RESPONSE,
    netRx := ambient.netRxSection}}
  let marked := if p.handshakeState != HANDSHAKE_CREATED_RESPONSE then
    {first with steps := first.steps.push {
      decision := .sessionNotConsumedResponse, outcome := p.handshakeState != HANDSHAKE_CONSUMED_RESPONSE,
      netRx := first.netRxSection}} else first
  have markHidden : marked.hidden = ambient.hidden := by unfold marked; split <;> rfl
  have markArmed : marked.allocArmed = ambient.allocArmed := by unfold marked; split <;> rfl
  have source : ((beginSession pid).run g).run ambient =
      (((do let key ← keypairCreate p.handshakeEntryPeer
            Index.sessionAfterCreate pid p.handshakeState key) : WG.M Bool).run g).run marked := by
    rcases accepted with created | consumed
    · rw [Index.beginSession_owner_source]
      simp [getPeer, getDev, device, resident, WG.andM, branch, AmbientM.branch,
        IndexOwner.peerWord, created, marked, first]
    · rw [Index.beginSession_owner_source]
      simp [getPeer, getDev, device, resident, WG.andM, branch, AmbientM.branch,
        IndexOwner.peerWord, consumed, marked, first, HANDSHAKE_CREATED_RESPONSE, HANDSHAKE_CONSUMED_RESPONSE]
  let consumed := {marked with hidden := some rest}
  have allocation : (((hiddenAlloc .kzallocKeypair : WG.M Bool).run g).run marked) =
      .ok ((false, g), consumed) := by
    change ((AmbientM.hiddenAlloc .kzallocKeypair).run marked).map
      (fun (value, after) => ((value, g), after)) = _
    rw [sessionAllocation_refused_run bytes rest width refused marked
      (markHidden.trans present) (by simpa [markArmed] using armed)]
    rfl
  let after := {consumed with steps := (consumed.steps.push {
    decision := .keypairCreateNoMem, outcome := true, netRx := consumed.netRxSection}).push {
    decision := .sessionNoKeypair, outcome := true, netRx := consumed.netRxSection}}
  refine ⟨after, ?_, rfl⟩
  rw [source]
  simp only [keypairCreate, Index.sessionAfterCreate, StateT.run_bind, allocation]
  simp [branch, AmbientM.branch, after]
  rfl

end Leanux.Proofs.WG.Noise
