import SourceAdapter
import PeerPhysicalSimulation

namespace Binary.LookupRelation
open Leanux Leanux.WG PeerCountPhase

/-- A focused represented count comes from a present source peer. It is
    not a freely supplied refcount operand or a live-peer assumption. -/
theorem project_peer_present (c : Config) (world : World) (v : View)
    (projected : project c world = some v) (pid : PeerId) (focused : c.focus.peer = some pid)
    (number : Nat) (count : v.count = some number) :
    ∃ device peer, world.wg.dev = some device ∧ device.peers.get? pid = some peer ∧ peer.refcount = number := by
  cases hasDevice : world.wg.dev with
  | none => simp [project, hasDevice] at projected
  | some device =>
    have countEq := congrArg (fun view : Option View => view.bind (·.count)) projected
    simp only [project, hasDevice, Option.bind_some, focused, Option.pure_def] at countEq
    change (device.peers.get? pid).map (·.refcount) = v.count at countEq
    rw [count] at countEq
    cases hasPeer : device.peers.get? pid with
    | none =>
      simp only [hasPeer, Option.map_none] at countEq
      cases countEq
    | some peer =>
      refine ⟨device, peer, rfl, hasPeer, ?_⟩
      simp only [hasPeer, Option.map_some,  Option.some.injEq] at countEq
      exact countEq

theorem R.peer_entry_data (c : Config) (world : World) (s : MachineState)
    (history : List MachineState) (seen : List LookupObservation.Point)
    (related : R c history seen s world) (initial : scan none history = none)
    (pid : PeerId) (focused : c.focus.peer = some pid) :
    ∃ device peer, world.wg.dev = some device ∧ device.peers.get? pid = some peer ∧
      c.peers pid ≠ 0 ∧ s.data.dmem.loadInt (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 =
        some (peer.refcount : Int) := by
  obtain ⟨v, projected, physical⟩ := related.2.1
  have represented := physical.2.2.2
  simp only [focused] at represented
  obtain ⟨number, count, nonnull, _⟩ := represented
  obtain ⟨device, peer, hasDevice, hasPeer, sourceCount⟩ := project_peer_present c world v projected pid focused number count
  refine ⟨device, peer, hasDevice, hasPeer, nonnull, ?_⟩
  rw [sourceCount]
  exact related.initial_count c history seen s world initial v projected pid focused number count

#print axioms project_peer_present
#print axioms R.peer_entry_data
end Binary.LookupRelation
