import Leanux.Proofs.WG.Noise.ReceptionCallerClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller
open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller

inductive PollResult where
  | empty
  | consumed (message : List UInt8) (source : SkbSource) (reception : ReceptionCall)

def PollResult.value : PollResult → Bool
  | .empty => false
  | .consumed _ _ _ => true

structure StepReceipt where
  entry : Campaign2.Snapshot
  poll : PollResult

def observeStepAt (entry : Campaign2.Snapshot) : WG.M StepReceipt := do
  match (← getDev).handshakeQueue.consume with
  | (none, _) =>
    _ ← branch .workerConsumed false
    return ⟨entry,.empty⟩
  | (some (msg,src), ring) =>
    _ ← branch .workerConsumed true
    modifyDev fun d => {d with handshakeQueue := ring}
    let call ← observeClassified msg src
    modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}
    return ⟨entry,.consumed msg src call⟩

def observeStep : WG.M StepReceipt := do
  let entry ← Campaign2.read
  observeStepAt entry

theorem observeStepAt_discard (entry : Campaign2.Snapshot) :
    (do let r ← observeStepAt entry; pure r.poll.value) = receiveStep := by
  rw [← HandshakeSources.step_original]
  simp only [observeStepAt,HandshakeSources.stepWith,bind_assoc]
  apply bind_congr
  intro d
  cases consumed : d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none => simp only [bind_assoc,pure_bind,PollResult.value,HandshakeSources.original]
    | some packet =>
      obtain ⟨msg,src⟩ := packet
      dsimp only
      rw [HandshakeSources.reception_original]
      simp only [bind_assoc,pure_bind,PollResult.value,HandshakeSources.original]
      apply bind_congr
      intro b
      apply bind_congr
      intro u
      rw [← observeClassified_discard msg src]
      simp only [bind_assoc,pure_bind]

theorem observeStep_discard :
    (do let r ← observeStep; pure r.poll.value) = receiveStep := by
  simp only [observeStep,bind_assoc]
  change (do let entry ← Campaign2.read
             (do let r ← observeStepAt entry; pure r.poll.value)) = _
  simp only [observeStepAt_discard]
  funext g ambient
  rfl

def ReceptionShape (msg : List UInt8) (src : SkbSource) (call : ReceptionCall) : Prop :=
  EntryShape msg call ∧
  GateEntryValid msg src call.gate ∧
  dispatchKind msg call.gate ≠ .wrongType ∧
  (call.receipts ≠ [] ↔ dispatchKind msg call.gate = .initiation ∨
    dispatchKind msg call.gate = .response) ∧
  ∀ r ∈ call.receipts, ReceiptValid r ∧ TagReceiptEffect r

def PollShape (entry : Campaign2.Snapshot) (poll : PollResult) : Prop :=
  ∃ d, entry.wg.device = some d ∧
    match poll with
    | .empty => d.handshakeQueue.consume.1 = none
    | .consumed msg src call =>
      d.handshakeQueue.consume.1 = some (msg,src) ∧ ReceptionShape msg src call

theorem observeStepAt_shape (g : WGWorld) (ambient : Ambient)
    (receipt : StepReceipt) (final : WGWorld) (after : Ambient)
    (run : observeStepAt (Campaign2.snapshot g ambient) g ambient =
      .ok ((receipt,final),after)) :
    receipt.entry = Campaign2.snapshot g ambient ∧ PollShape receipt.entry receipt.poll := by
  change (getDev g ambient >>= _) = _ at run
  cases device : g.dev with
  | none =>
    have read : getDev g ambient =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      change ((getDev.run g).run ambient) = _
      simp [getDev,device,invariant,AmbientM.invariant]
      rfl
    rw [read] at run
    cases run
  | some d =>
    have read : getDev g ambient = .ok ((d,g),ambient) := by
      change ((getDev.run g).run ambient) = _
      simp [getDev,device,invariant,AmbientM.invariant]
    simp only [read,bind,Except.bind] at run
    cases selected : d.handshakeQueue.consume with
    | mk packet ring =>
      cases packet with
      | none =>
        simp only [selected] at run
        change Except.ok
          (((⟨Campaign2.snapshot g ambient,.empty⟩ : StepReceipt),g),
            {ambient with steps := (ambient.steps.push
              {decision := .workerConsumed,outcome := false,netRx := ambient.netRxSection})}) = _ at run
        cases run
        exact ⟨rfl,d,device,congrArg Prod.fst selected⟩
      | some packet =>
        obtain ⟨msg,src⟩ := packet
        simp only [selected] at run
        let next : WGWorld := {g with dev := g.dev.map fun d => {d with handshakeQueue := ring}}
        let inputs : Ambient := {ambient with steps := (ambient.steps.push
          {decision := .workerConsumed,outcome := true,netRx := ambient.netRxSection})}
        change (observeClassified msg src next inputs >>= fun ((call,current),tail) =>
          Except.ok
            (((⟨Campaign2.snapshot g ambient,.consumed msg src call⟩ : StepReceipt),
              {current with dev := current.dev.map fun (d : Device) =>
                {d with handshakeQueueLen := d.handshakeQueueLen - 1}}),tail)) = _ at run
        cases received : observeClassified msg src next inputs with
        | error stop => rw [received] at run; cases run
        | ok out =>
          obtain ⟨⟨call,current⟩,tail⟩ := out
          rw [received] at run
          obtain ⟨shape,gateValid,wrong,nonempty,effects⟩ :=
            original_reception_dispatch msg src next inputs call current tail True.intro received
          cases run
          exact ⟨rfl,d,device,congrArg Prod.fst selected,shape,gateValid,wrong,nonempty,effects⟩

/- Source equations for the exact one-step state handoff. -/
def pollAmbient (ambient : Ambient) (consumed : Bool) : Ambient :=
  {ambient with steps := (ambient.steps.push
    {decision := .workerConsumed,outcome := consumed,netRx := ambient.netRxSection})}

def dequeueWorld (g : WGWorld) (ring : PtrRing (List UInt8 × SkbSource)) : WGWorld :=
  {g with dev := g.dev.map fun d => {d with handshakeQueue := ring}}

def decrementWorld (g : WGWorld) : WGWorld :=
  {g with dev := g.dev.map fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}}

theorem observeStep_empty_run (g : WGWorld) (ambient : Ambient) (d : Device)
    (ring : PtrRing (List UInt8 × SkbSource)) (device : g.dev = some d)
    (selected : d.handshakeQueue.consume = (none,ring)) :
    observeStep g ambient =
      .ok ((⟨Campaign2.snapshot g ambient,.empty⟩,g),pollAmbient ambient false) := by
  have read : (getDev.run g).run ambient = .ok ((d,g),ambient) := by
    simp [getDev,device]
  change ((getDev.run g).run ambient >>= _) = _
  simp only [read,bind,Except.bind,selected]
  rfl

theorem observeStep_consumed_run (g : WGWorld) (ambient : Ambient) (d : Device)
    (msg : List UInt8) (src : SkbSource) (ring : PtrRing (List UInt8 × SkbSource))
    (device : g.dev = some d) (selected : d.handshakeQueue.consume = (some (msg,src),ring)) :
    observeStep g ambient =
      (observeClassified msg src (dequeueWorld g ring) (pollAmbient ambient true)).map
        (fun ((call,current),tail) =>
          ((⟨Campaign2.snapshot g ambient,.consumed msg src call⟩,decrementWorld current),tail)) := by
  have read : (getDev.run g).run ambient = .ok ((d,g),ambient) := by
    simp [getDev,device]
  change ((getDev.run g).run ambient >>= _) = _
  simp only [read,bind,Except.bind,selected]
  change (observeClassified msg src (dequeueWorld g ring) (pollAmbient ambient true) >>= _) = _
  cases observeClassified msg src (dequeueWorld g ring) (pollAmbient ambient true) <;> rfl


end Leanux.Proofs.WG.Noise.ReceiveStepCaller
