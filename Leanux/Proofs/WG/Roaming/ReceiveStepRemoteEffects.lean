import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

theorem call_origin (call : Call)
    (facts : Product.HandshakeFinalRemotes call.message call.source call.entry call.receipt call.finish)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (present : remoteMap call.finish.toSnapshot pid = some remote) :
    remoteMap call.entry.toSnapshot pid = some remote ∨ call.Authenticated pid remote := by
  obtain ⟨msg,src,entry,finish,receipt⟩ := call
  cases receipt with
  | other =>
    exact Or.inl ((congrFun facts.2.2 pid).symm.trans present)
  | initiation observed =>
    obtain ⟨kind,authenticated,candidate,atCut,returned,same,effect⟩ := facts
    cases returned
    cases candidate with
    | none => exact Or.inl ((congrFun effect pid).symm.trans present)
    | some cut =>
      have origin := effect pid remote present
      by_cases selected : pid = cut.consumed.pid
      · right
        have remoteEq : remote = destination (sourceEndpoint src) := by
          exact (Option.some.inj (by simpa only [updateRemote,selected,ite_true] using origin)).symm
        obtain ⟨actual,actualCut,receiptEq,auth⟩ := authenticated
        cases receiptEq
        obtain ⟨atSetter,valid⟩ := auth cut rfl
        exact ⟨kind,cut,atCut,rfl,atSetter,valid,selected,remoteEq⟩
      · left
        simpa only [updateRemote,selected,ite_false] using origin
  | response observed =>
    obtain ⟨kind,authenticated,candidate,atCut,returned,same,effect⟩ := facts
    cases returned
    cases candidate with
    | none => exact Or.inl ((congrFun effect pid).symm.trans present)
    | some cut =>
      have origin := effect pid remote present
      by_cases selected : pid = cut.consumed.input.pid
      · right
        have remoteEq : remote = destination (sourceEndpoint src) := by
          exact (Option.some.inj (by simpa only [updateRemote,selected,ite_true] using origin)).symm
        obtain ⟨actual,actualCut,receiptEq,auth⟩ := authenticated
        cases receiptEq
        obtain ⟨atSetter,valid⟩ := auth cut rfl
        exact ⟨kind,cut,atCut,rfl,atSetter,valid,selected,remoteEq⟩
      · left
        simpa only [updateRemote,selected,ite_false] using origin

theorem observation_origin (q : Observation) (facts : q.Facts)
    (pid : PeerId) (remote : Nat × Nat × Nat × Nat)
    (present : remoteMap q.finish.toSnapshot pid = some remote) :
    remoteMap q.entry.toSnapshot pid = some remote ∨ q.Cause pid remote := by
  obtain ⟨d,device,facts⟩ := facts
  cases selected : q.call with
  | none =>
    rw [selected] at facts
    exact Or.inl ((congrFun facts.2.2 pid).symm.trans present)
  | some call =>
    rw [selected] at facts
    have atCall : remoteMap call.finish.toSnapshot pid = some remote :=
      (congrFun facts.2.2.2.1 pid).symm.trans present
    cases call_origin call facts.2.2.2.2 pid remote atCall with
    | inl old => exact Or.inl ((congrFun facts.2.2.1 pid).symm.trans old)
    | inr authenticated => exact Or.inr ⟨call,selected,authenticated⟩

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
