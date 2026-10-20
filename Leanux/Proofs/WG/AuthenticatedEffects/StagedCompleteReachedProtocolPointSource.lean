import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSource

/-! Protocol points come from the fixed caller tree and actual native socket/read/write points. Each point retains its original continuation, including before a later failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action → World → History → World → History → Prop where
  | entry (source : Shape action) : Point source w h w h
  | returned (source : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) : Point source w h u middle
  | native {α : Type} {body : WG.M α} {source : PeerMetadata.Shape body} {w : World}
      (point : PeerMetadata.Point source w.wg w.ambient v b) :
      Point (.native body source) w h {w with wg:=v,ambient:=b} h
  | socket {w : World} (point : NativeSocket.Point args w.wg w.ambient v b) :
      Point (.socket args) w h {w with wg:=v,ambient:=b} h
  | left {body : PrefixM Event α} {next : α→PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w h u middle) : Point (.bind head tail) w h u middle
  | right {body : PrefixM Event α} {next : α→PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefix body w h=(.ok (value,u),middle))
      (point : Point (tail value) u middle v last) : Point (.bind head tail) w h v last

theorem Point.remaining {α : Type} {action : PrefixM Event α} {source : Shape action}
    (point : Point source w h u middle) : ∃remaining,runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | native point=>exact point.observed_remaining _
  | socket point=>exact socket_remaining point _
  | left tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= _,Scheduler.bind_run_equal _ same⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by rw [runPrefix_bind,leading];exact same⟩

def RootPoint (pid : PeerId) (bytes : Key) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  Point (canonical pid bytes) w h u middle

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
