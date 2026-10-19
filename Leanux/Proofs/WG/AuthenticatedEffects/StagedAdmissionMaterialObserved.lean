import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionMaterialSource

/-! Material checkpoints are connected to the actual whole enriched front.
This independent contract is joined by its exact run, including Stop prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

theorem front_checked (input : Input) (w : WGWorld) (a : Ambient) (history : List Event) :
    let result := runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a history
    Checked (history ++ [.transmitInput input]) w result.2 ∧
      match result.1 with
      | .error _ => True
      | .ok ((_,v),_) => view v = view w := by
  obtain ⟨_,_,checked,normal⟩ := body_checked (base := history ++ [.transmitInput input]) (initial := w)
    input.family input.address input.packets input.mtu w a (history ++ [.transmitInput input])
    ⟨Checked.empty _ _,rfl⟩
  rw [Front.front_run]
  cases executed : runWGPrefix (body input.family input.address input.packets input.mtu)
      w a (history ++ [.transmitInput input]) with
  | mk result hist =>
    change runPrefix ((body input.family input.address input.packets input.mtu).run w)
      a (history ++ [.transmitInput input]) = _ at executed
    rw [executed] at checked normal
    cases result with
    | error stop => exact ⟨checked,True.intro⟩
    | ok out =>
      rcases out with ⟨⟨value,v⟩,b⟩
      exact ⟨checked.append (routedEvent input ⟨value,w,v,a,b⟩) True.intro,normal.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
