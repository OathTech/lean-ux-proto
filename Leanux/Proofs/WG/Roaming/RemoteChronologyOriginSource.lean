import Leanux.Proofs.WG.Roaming.RemoteChronologyOriginBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged

theorem latest_of_order (trace : Runner.Trace) (placeholders : Bool)
    (events : List RemoteDriver.Event) (final : RemoteMap)
    (actual : events = RemoteDriver.Runner.history trace placeholders)
    (safe : RemoteDriver.Safe events)
    (ordered : Last Driver.effect (fun _ => none) events final)
    (pid : PeerId) (remote : Remote) (present : final pid = some remote) :
    ∃ q : LatestOrigin, q.Valid trace placeholders pid remote ∧ q.origin.Facts pid remote := by
  obtain ⟨before,event,after,position,set,last⟩ := empty_origin ordered pid remote present
  have exactRx : events.filterMap RemoteDriver.rxEvent = ConfirmationOrder.history trace placeholders := by
    rw [actual]
    exact RemoteDriver.Runner.history_rx trace placeholders
  obtain ⟨origin,matched,facts,index⟩ := RemoteProvenance.origin_at_cause trace placeholders events
    exactRx safe event before after position pid remote (Driver.effect_cause event pid remote set) [event] (by simp)
  exact ⟨⟨before.length,origin⟩,⟨before,event,after,actual.symm.trans position,rfl,set,last,matched,index⟩,facts⟩

end Leanux.Proofs.WG.Roaming.RemoteChronology
