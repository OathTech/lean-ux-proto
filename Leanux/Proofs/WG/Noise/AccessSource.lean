import Leanux.Proofs.WG.Noise.Execution

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem getPeer_spec (pid : PeerId) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P w ∧ peerAt w pid = some p⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient p g' ambient' pre run
  cases device : g.dev with
  | none =>
    simp [getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, device, peer, invariant, AmbientM.invariant] at run
      cases run
    | some found =>
      simp [getPeer, getDev, device, peer] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨pre, by simp [peerAt, device, peer]⟩

theorem setPeer_spec (pid : PeerId) (p : Peer) (P : Peer → Prop) :
    ⦃fun w => ⌜(peerAt w pid).isSome ∧ P p⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜∃ p', peerAt w pid = some p' ∧ P p'⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result g' ambient' pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device => {d with peers := d.peers.insert pid p})}), ambient) = _ at run
  cases run
  cases device : g.dev with
  | none => simp [peerAt, device] at pre
  | some d => exact ⟨p, by simp [peerAt], pre.2⟩

end Leanux.Proofs.WG.Noise
