import Leanux.Proofs.WG.Roaming.ReceiveStepSetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG

/-- A completed handshake's entire destination effect is its single selected
setter followed by retention, including the case of an already equal value. -/
theorem call_setter_effect (call : Call)
    (facts : Product.HandshakeFinalRemotes call.message call.source call.entry call.receipt call.finish) :
    RemoteRetained (setterMap (remoteMap call.entry.toSnapshot) call.setter)
      (remoteMap call.finish.toSnapshot) := by
  obtain ⟨msg,src,entry,finish,receipt⟩ := call
  cases receipt with
  | other => exact RemoteRetained.of_eq facts.2.2
  | initiation observed =>
    obtain ⟨_,_,candidate,atCut,returned,_,effect⟩ := facts
    cases returned
    cases candidate with
    | none => exact RemoteRetained.of_eq effect
    | some cut => exact effect
  | response observed =>
    obtain ⟨_,_,candidate,atCut,returned,_,effect⟩ := facts
    cases returned
    cases candidate with
    | none => exact RemoteRetained.of_eq effect
    | some cut => exact effect

/-- Selecting a setter identifies the authenticated prefix even when its
remote was already equal to the incoming packet's source. -/
theorem call_setter_authenticated (call : Call)
    (facts : Product.HandshakeFinalRemotes call.message call.source call.entry call.receipt call.finish)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (selected : call.setter = some (pid,remote)) : call.Authenticated pid remote := by
  obtain ⟨msg,src,entry,finish,receipt⟩ := call
  cases receipt with
  | other => cases selected
  | initiation observed =>
    obtain ⟨kind,authenticated,candidate,atCut,returned,_,_⟩ := facts
    cases returned
    cases candidate with
    | none => cases selected
    | some cut =>
      have equal : (cut.consumed.pid,destination (sourceEndpoint src)) = (pid,remote) :=
        Option.some.inj selected
      cases equal
      obtain ⟨actual,actualCut,receiptEq,auth⟩ := authenticated
      cases receiptEq
      obtain ⟨atSetter,valid⟩ := auth cut rfl
      exact ⟨kind,cut,atCut,rfl,atSetter,valid,rfl,rfl⟩
  | response observed =>
    obtain ⟨kind,authenticated,candidate,atCut,returned,_,_⟩ := facts
    cases returned
    cases candidate with
    | none => cases selected
    | some cut =>
      have equal : (cut.consumed.input.pid,destination (sourceEndpoint src)) = (pid,remote) :=
        Option.some.inj selected
      cases equal
      obtain ⟨actual,actualCut,receiptEq,auth⟩ := authenticated
      cases receiptEq
      obtain ⟨atSetter,valid⟩ := auth cut rfl
      exact ⟨kind,cut,atCut,rfl,atSetter,valid,rfl,rfl⟩

theorem observation_setter_effect (q : Observation) (facts : q.Facts) :
    RemoteRetained (setterMap (remoteMap q.entry.toSnapshot) q.setter)
      (remoteMap q.finish.toSnapshot) := by
  obtain ⟨d,_,facts⟩ := facts
  cases selected : q.call with
  | none =>
    rw [selected] at facts
    simpa only [Observation.setter,selected,Option.bind_none,setterMap] using
      RemoteRetained.of_eq facts.2.2
  | some call =>
    rw [selected] at facts
    have effect := call_setter_effect call facts.2.2.2.2
    rw [facts.2.2.1,← facts.2.2.2.1] at effect
    simpa only [Observation.setter,selected,Option.bind_some] using effect

theorem observation_setter_authenticated (q : Observation) (facts : q.Facts)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (selected : q.setter = some (pid,remote)) : q.Cause pid remote := by
  obtain ⟨d,_,facts⟩ := facts
  cases picked : q.call with
  | none => simp only [Observation.setter,picked,Option.bind_none] at selected; cases selected
  | some call =>
    rw [picked] at facts
    simp only [Observation.setter,picked,Option.bind_some] at selected
    exact ⟨call,picked,call_setter_authenticated call facts.2.2.2.2 pid remote selected⟩

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
