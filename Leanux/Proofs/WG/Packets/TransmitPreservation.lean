import Leanux.Proofs.WG.Packets.TransmitChecks
import Leanux.Proofs.WG.Packets.TransmitObserver

/-! Native composition retains routing and every earlier handoff certificate.
The contracts are about actual native WG/Ambient observers, including Stops. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Packets AllowedIps

/-- The tail adds no transmit events; existing positional certificates survive
its actual output prefix even if no final native state is returned. -/
theorem transmitWith_checks (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int)
    (appends : StateAppends front) (frame : StateHistoryFrame RoutingJoint.routingEvent front)
    (source : ErasesStatePrefix front (txFront family addr packets mtu))
    (w : WGWorld) (ambient : Ambient) (h : List Event)
    (routing : GlobalCompletionState initial (routes h) w) (checked : Checks initial h) :
    Checks initial (runWGPrefix (transmitWith family addr packets mtu front tail) w ambient h).2 := by
  have captured := observeFront_checks family addr packets mtu front appends frame source w ambient h routing checked
  change Checks initial (runStatePrefix (transmitWith family addr packets mtu front tail) w ambient h).2
  rw [transmitWith,runStatePrefix_bind]
  simp only [runWGPrefix] at captured
  cases run : runStatePrefix (observeFront family addr packets mtu front) w ambient h with
  | mk result hist =>
    simp only [run] at captured
    cases result with
    | error stop => exact captured
    | ok out =>
      rcases out with ⟨⟨result,v⟩,after⟩
      cases result with
      | error err => exact captured
      | ok pid => exact captured.focusedOld (tail pid) v after

/-- Normal-state routing follows the original erasure and routing relation;
failed-prefix safety follows the actual captured events, with no final state. -/
theorem native_preserves (initial : FlatTable × FlatTable) (g : WGPrefix Event α) (a : WG.M α)
    (appends : StateAppends g) (source : ErasesStatePrefix g a)
    (routing : RetainsRoutingCall a)
    (journal : ∀ w ambient h, routes (runWGPrefix g w ambient h).2 = routes h)
    (captures : ∀ w ambient h, GlobalCompletionState initial (routes h) w → Checks initial h →
      Checks initial (runWGPrefix g w ambient h).2) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial (routes h) w ∧ Checks initial h)
      (Safe initial) g := by
  intro w ambient h hi
  obtain ⟨suffix,hs⟩ := appends w ambient h
  have routesSame := journal w ambient h
  change routes (runPrefix (g.run w) ambient h).2 = routes h at routesSame
  have checks := captures w ambient h hi.1 hi.2
  refine ⟨suffix,hs,⟨?_,checks⟩,?_⟩
  · exact routesSame ▸ hi.1.1
  · cases run : (runPrefix (g.run w) ambient h).1 with
    | error stop => trivial
    | ok out =>
      rcases out with ⟨⟨value,v⟩,after⟩
      have sourceRun : (a.run w).run ambient = .ok ((value,v),after) :=
        (source w ambient h).symm.trans run
      have retained := (ProjectedAction.iff_run_ambient _ _ _).mp routing w ambient value v after sourceRun
      refine ⟨⟨?_,?_⟩,checks⟩
      · exact routesSame ▸ hi.1.1
      · simpa only [routesSame,id] using hi.1.2.retains retained

end Leanux.Proofs.WG.TransmitJoint
