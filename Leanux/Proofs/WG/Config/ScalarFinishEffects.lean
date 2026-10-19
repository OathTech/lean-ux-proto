import Leanux.Proofs.WG.Config.ScalarFinishModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarFinish
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention

theorem selected_retained {initial final : Map} {pid : PeerId} {expected : Cell}
    (kept : Retained initial final) (selected : Selected pid expected initial) :
    Selected pid expected final := by
  intro c present
  exact selected c (kept pid c present)

theorem selected_initial (pid : PeerId) (c : Cell) (initial : Map)
    (present : initial pid=some c) : Selected pid c initial := by
  intro other found
  exact Option.some.inj (found.symm.trans present)

theorem observation_resident (s : Campaign2.Snapshot) (pid : PeerId) (expected : Cell)
    (present : observation s pid=some expected) :
    ∃ d p,s.wg.device=some d ∧ d.peers[pid]?=some p ∧ cell p=expected := by
  cases hd : s.wg.device with
  | none => simp [observation,peerValues,hd] at present
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [observation,peerValues,hd,hp] at present
    | some p =>
      exact ⟨d,p,rfl,hp,by simpa only [observation,peerValues,hd,Option.bind_some,hp,
        Option.map_some,Option.some.injEq] using present⟩

end Leanux.Proofs.WG.Config.ScalarFinish
