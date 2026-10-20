import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteInitialized

/-! The keepalive setter uses the peer saved before its decisions. Its source
points record that read and the original write, without a field-frame premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigSaved
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
abbrev History := List Event

def decision (p : Peer) (running : Bool) (interval : Nat) : WG.M Bool :=
  WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
    (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))

def native (pid : PeerId) (running : Bool) (interval : Nat) : WG.M Bool := do
  let p ← getPeer pid
  let send ← decision p running interval
  setPeer pid {p with persistentKeepaliveInterval:=interval}
  pure send

def observer (pid : PeerId) (running : Bool) (interval : Nat) : WGPrefix Event Bool := do
  let p ← liftWGPrefix (getPeer pid)
  let send ← liftWGPrefix (decision p running interval)
  liftWGPrefix (setPeer pid {p with persistentKeepaliveInterval:=interval})
  pure send

def read (pid : PeerId) : PrefixM Event Peer := liftWGObserver (liftWGPrefix (getPeer pid))
def decide (p : Peer) (running : Bool) (interval : Nat) : PrefixM Event Bool :=
  liftWGObserver (liftWGPrefix (decision p running interval))
def write (pid : PeerId) (p : Peer) (interval : Nat) : PrefixM Event Unit :=
  liftWGObserver (liftWGPrefix (setPeer pid {p with persistentKeepaliveInterval:=interval}))
def action (pid : PeerId) (running : Bool) (interval : Nat) : PrefixM Event Bool :=
  liftWGObserver (observer pid running interval)

theorem source (pid : PeerId) (running : Bool) (interval : Nat) :
    action pid running interval=(read pid >>= fun p=>decide p running interval >>= fun send=>
      write pid p interval >>= fun _=>pure send) := by
  simp only [action,observer,liftWGObserver_bind,liftWGObserver_pure]
  rfl

inductive Point (pid : PeerId) (running : Bool) (interval : Nat) (w : World) (h : History) :
    World → History → Prop where
  | entry : Point pid running interval w h w h
  | read (got : runPrefix (ConfigSaved.read pid) w h=(.ok (p,u),middle)) :
      Point pid running interval w h u middle
  | decided (got : runPrefix (ConfigSaved.read pid) w h=(.ok (p,u),middle))
      (guarded : runPrefix (decide p running interval) u middle=(.ok (send,v),last)) :
      Point pid running interval w h v last
  | written (got : runPrefix (ConfigSaved.read pid) w h=(.ok (p,u),middle))
      (guarded : runPrefix (decide p running interval) u middle=(.ok (send,v),last))
      (stored : runPrefix (write pid p interval) v last=(.ok ((),x),final)) :
      Point pid running interval w h x final
  | returned (performed : runPrefix (action pid running interval) w h=(.ok (send,u),middle)) :
      Point pid running interval w h u middle

theorem Point.remaining (point : Point pid running interval w h u middle) :
    ∃remaining,runPrefix (action pid running interval) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | read got=>exact ⟨_,by rw [source,runPrefix_bind,got]⟩
  | decided got guarded=>
      rename_i prior p v send
      exact ⟨write pid p interval >>= fun _=>pure send,by
        simp only [source,runPrefix_bind,got,guarded]⟩
  | written got guarded stored=>
      rename_i prior p v later send x
      exact ⟨pure send,by simp only [source,runPrefix_bind,got,guarded,stored]⟩
  | returned performed=>exact ⟨pure _,performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigSaved
