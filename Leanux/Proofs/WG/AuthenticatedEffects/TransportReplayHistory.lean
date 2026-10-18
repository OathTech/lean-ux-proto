import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationFrames

/-! Actual indexed replay receipts carry the earlier packet authentication
publication. The journal order is checked before the counter receipt is emitted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
set_option maxHeartbeats 600000
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {h suffix history pre post : List E}
  {event : E} {r : TransportDriver.Replay}

def Certified (history : List TransportDriver.OriginEvent) (r : TransportDriver.Replay) : Prop :=
  r.Valid ∧ r.Selected ∧ TransportPublication.Anchor history r.skb r.packet r.run.before.wg

def Checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (pre : List E) (event : E) : Prop :=
  ∀ r, replay event = some r → Certified (pre.filterMap origin) r

def Safe (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (history : List E) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked origin replay pre event

def Inv (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (history : List E) (w : World) : Prop :=
  TransportPublication.Inv (history.filterMap origin) w.wg ∧ Safe origin replay history

def Picked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (skb : SkbId) (pkt : RxPacket)
    (h : List E) (w : World) : Prop :=
  Inv origin replay h w ∧ (RxDisposition.nativeRxStore w.wg).2 skb = some pkt

theorem Safe.append (hi : Safe origin replay h)
    (next : ∀ pre event post, suffix = pre ++ event :: post → Checked origin replay (h ++ pre) event) :
    Safe origin replay (h ++ suffix) := by
  unfold Safe at *
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked origin replay) h suffix hi next

theorem Safe.quiet (hi : Safe origin replay h) (quiet : suffix.filterMap replay = []) :
    Safe origin replay (h ++ suffix) := by
  apply hi.append
  intro pre event post position r recorded
  have member : event ∈ suffix := by rw [position]; simp
  have found : r ∈ suffix.filterMap replay := List.mem_filterMap.mpr ⟨event,member,recorded⟩
  simp [quiet] at found

theorem counter_checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (skb : SkbId) (pkt : RxPacket) (crypted : pkt.state = .crypted) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (TransportDriver.counter record skb pkt) (fun _ => Inv origin replay) := by
  intro w h hi
  rw [TransportDriver.counter_run]
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error err => exact ⟨[],by simp,hi.1.2,True.intro⟩
  | ok out =>
    rcases out with ⟨value,v⟩
    let receipt : TransportDriver.Replay := ⟨skb,pkt,⟨value,w,v⟩⟩
    have certified : Certified (h.filterMap origin) receipt :=
      ⟨run,⟨hi.2,crypted⟩,hi.1.1 skb pkt hi.2 crypted⟩
    have safe : Safe origin replay (h ++ [record receipt]) := by
      apply hi.1.2.append
      intro pre event post position r recorded
      cases pre with
      | nil =>
        cases position
        have eq : receipt = r := Option.some.inj ((inverse receipt).symm.trans recorded)
        subst r
        simpa only [List.append_nil] using certified
      | cons x xs =>
        have lengths := congrArg List.length position
        simp only [List.length_append,List.length_cons,List.length_nil] at lengths
        omega
    have kept := (hoare_iff_run _ _ _).mp
      (TransportPublication.counterValidate_preserves pkt.keypair pkt.nonce (h.filterMap origin))
      w value v hi.1.1 run
    refine ⟨[record receipt],rfl,safe,?_,safe⟩
    simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,quiet,
      Option.toList_none,List.nil_append,List.append_nil] using kept

/-- Concrete receipt extraction requires a history proved safe at the same
execution; no completed consumer or later endpoint receipt is assumed. -/
theorem replay_authenticated (safe : Safe origin replay history)
    (position : history = pre ++ event :: post) (recorded : replay event = some r) :
    Certified (pre.filterMap origin) r := safe pre event post position r recorded

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
