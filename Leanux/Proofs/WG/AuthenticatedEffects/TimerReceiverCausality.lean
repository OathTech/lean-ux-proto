import Leanux.Proofs.WG.AuthenticatedEffects.TimerReceiverCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.WorkTimerCausality
import Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatchScope

/-! Native receiver-to-timer cause transport. The receiver's output carrier is
derived from its input inventory; selection refers to the actual current wheel
occurrence and its own recorded arm. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerInventory
open Leanux Leanux.WG Leanux.Proofs.Logged

def NoPending (w : WGWorld) : Prop :=
  ∀ pid timer stamp expires entry, ¬TimerSlots.Pending w pid timer stamp expires entry

theorem empty_carrier (w : WGWorld) (empty : NoPending w) : TimerSlots.Carrier [] w :=
  fun pid timer stamp expires entry pending => False.elim (empty pid timer stamp expires entry pending)

theorem receive_completed (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (h : List TimerRoot.Event) (input : TimerSlots.Carrier h w)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    TimerSlots.Carrier (runWGPrefix (WorkRoot.receive msg src) w a h).2 v := by
  obtain ⟨_,_,_,out⟩ := receive_preserves msg src w a h input
  have observed : (runWGPrefix (WorkRoot.receive msg src) w a h).1 = .ok (((),v),b) :=
    (WorkRoot.receive_erases msg src w a h).trans run
  change (runPrefix ((WorkRoot.receive msg src).run w) a h).1 = _ at observed
  rw [observed] at out
  exact out

theorem receive_from_empty (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (empty : NoPending w)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    TimerSlots.Carrier (runWGPrefix (WorkRoot.receive msg src) w a []).2 v :=
  receive_completed msg src w v a b [] (empty_carrier w empty) run

theorem receiver_then_selection_authenticated (msg : Key) (src : SkbSource)
    (before : WGWorld) (ambient : Ambient) (r : TimerDispatch.Selection)
    (empty : NoPending before)
    (received : ((receiveHandshakePacket msg src).run before).run ambient =
      .ok (((),r.before.wg),r.before.ambient))
    (selected : r.Valid) :
    ∃ stamp expires arm pre post,
      TimerSlots.Pending r.before.wg r.peer r.timer stamp expires r.entry ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .armed arm :: post ∧
      arm.Native ∧ TimerSlots.Changed arm ∧ arm.peer = r.peer ∧ arm.timer = r.timer ∧
      TimerSlots.Pending arm.run.after r.peer r.timer stamp expires r.entry ∧
      WorkRoot.AuthenticatedAt pre arm.origin arm.kind arm.peer := by
  have carrier := receive_from_empty msg src before r.before.wg ambient r.before.ambient empty received
  obtain ⟨stamp,expires,pending,arm,recorded,peer,timer,armed⟩ :=
    TimerDispatch.selection_cause r selected carrier
  obtain ⟨pre,post,position,native,changed⟩ := recorded
  exact ⟨stamp,expires,arm,pre,post,pending,position,native,changed,peer,timer,armed,
    (WorkTimer.armed_authenticated msg src before ambient pre post arm position).2⟩

theorem receiver_then_scope_authenticated (msg : Key) (src : SkbSource)
    (before : WGWorld) (ambient : Ambient) (w : World) (d : Device) (j : UInt64)
    (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (record : TimerDispatch.Selection → E) (body : PrefixM E α) (h : List E)
    (appends : Appends body) (empty : NoPending before)
    (received : ((receiveHandshakePacket msg src).run before).run ambient = .ok (((),w.wg),w.ambient))
    (saved : w.wg.dev = some d) (selected : TimerWheel.nextDue d j = some (pid,timer,entry)) :
    ∃ suffix stamp expires arm pre post,
      (runPrefix (TimerDispatch.scope record d j pid timer entry body) w h).2 =
        h ++ record ⟨d,j,pid,timer,entry,w⟩ :: suffix ∧
      TimerSlots.Pending w.wg pid timer stamp expires entry ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .armed arm :: post ∧
      arm.Native ∧ TimerSlots.Changed arm ∧ arm.peer = pid ∧ arm.timer = timer ∧
      TimerSlots.Pending arm.run.after pid timer stamp expires entry ∧
      WorkRoot.AuthenticatedAt pre arm.origin arm.kind arm.peer := by
  obtain ⟨suffix,history⟩ := TimerDispatch.scope_entry record d j pid timer entry appends w h
  obtain ⟨stamp,expires,arm,pre,post,pending,position,native,changed,peer,kind,armed,cause⟩ :=
    receiver_then_selection_authenticated msg src before ambient ⟨d,j,pid,timer,entry,w⟩ empty received
      ⟨saved,selected⟩
  exact ⟨suffix,stamp,expires,arm,pre,post,history,pending,position,native,changed,peer,kind,armed,cause⟩

end Leanux.Proofs.WG.AuthenticatedEffects.TimerInventory
