import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueReceiver

/-! Concrete receiver-to-worker causality. An empty native input queue supplies
its carrier; no output inventory is assumed. The worker receipt is retained
before its suffix, so authentication provenance survives an internal Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem receive_completed (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (h : List TimerRoot.Event) (input : Inventory h w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    Inventory (runWGPrefix (WorkRoot.receive msg src) w a h).2 v b := by
  obtain ⟨_,_,_,out⟩ := receive_preserves msg src w a h input
  have observed : (runWGPrefix (WorkRoot.receive msg src) w a h).1 = .ok (((),v),b) :=
    (WorkRoot.receive_erases msg src w a h).trans run
  change (runPrefix ((WorkRoot.receive msg src).run w) a h).1 = _ at observed
  rw [observed] at out
  exact out

theorem receive_from_empty (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (empty : queue w = [])
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    ∃ tickets, Carrier (runWGPrefix (WorkRoot.receive msg src) w a []).2 tickets v :=
  receive_completed msg src w v a b [] ⟨[],Carrier.empty w empty⟩ run

theorem receiver_then_dispatch_authenticated (msg : Key) (src : SkbSource)
    (before : WGWorld) (ambient : Ambient) (w : World)
    (empty : queue before = [])
    (received : ((receiveHandshakePacket msg src).run before).run ambient = .ok (((),w.wg),w.ambient))
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix dispatch w []).2) :
    ∃ tickets ticket rest pre post,
      Carrier (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 tickets w.wg ∧
      Selected tickets r.value ticket rest ∧ ticket.peer = r.value ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .queued ticket.receipt :: post ∧
      pre.length = ticket.index ∧
      WorkRoot.AuthenticatedAt pre ticket.receipt.origin ticket.receipt.kind ticket.peer := by
  obtain ⟨tickets,carrier⟩ := receive_from_empty msg src before w.wg ambient w.ambient empty received
  obtain ⟨ticket,rest,pre,post,selected,peer,position,index,cause⟩ :=
    dispatch_authenticated msg src before ambient w tickets carrier r reached
  exact ⟨tickets,ticket,rest,pre,post,carrier,selected,peer,position,index,cause⟩

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
