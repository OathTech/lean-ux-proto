import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPoll

/-! The exact newly appended replay receipt is retained through native guards
up to the consumer entry. No prior matching authentication substitutes for the
current poll's own counter result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {record : TransportDriver.Replay → E}
  {pkt : RxPacket} {result : Bool}

def Returned (origin : E → Option TransportDriver.OriginEvent)
    (record : TransportDriver.Replay → E) (pkt : RxPacket) (result : Bool) (h : List E) : Prop :=
  ∃ pre r, h = pre ++ [record r] ∧ r.packet = pkt ∧ r.run.value = result ∧
    Certified (pre.filterMap origin) r

def AtCounter (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (pkt : RxPacket) (result : Bool) (h : List E) (w : World) : Prop :=
  Inv origin replay h w ∧ Returned origin record pkt result h

theorem counter_returned (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (skb : SkbId) (pkt : RxPacket) (crypted : pkt.state = .crypted) :
    PrefixEnsures (Picked origin replay skb pkt) (Safe origin replay)
      (TransportDriver.counter record skb pkt) (AtCounter origin replay record pkt) := by
  intro w h hi
  obtain ⟨suffix,appended,safe,normal⟩ := counter_checked origin replay record inverse quiet skb pkt crypted w h hi
  refine ⟨suffix,appended,safe,?_⟩
  rw [TransportDriver.counter_run] at normal ⊢
  cases run : (liftWG (counterValidate pkt.keypair pkt.nonce)).run w with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,v⟩
    simp only [run] at normal ⊢
    refine ⟨normal,h,⟨skb,pkt,⟨value,w,v⟩⟩,rfl,rfl,rfl,?_⟩
    exact ⟨run,⟨hi.2,crypted⟩,hi.1.1 skb pkt hi.2 crypted⟩

theorem atCounter_native (action : WG.M α) (frame : SameView RxDisposition.nativeRxStore action) :
    PrefixPreserves (AtCounter origin replay record pkt result) (Safe origin replay)
      (liftPrefix (liftWG action)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
  intro h w x v hi run
  have kept := (hoare_iff_run _ _ _).mp
    (PublicationPoll.native_product _ _ (TransportPublication.preserves_of_rx action frame (h.filterMap origin)))
    w x v hi.1.1 run
  exact ⟨⟨kept,hi.1.2⟩,hi.2⟩

theorem invalid_bind (f : Bool → PrefixM E α)
    (next : ∀ bad, bad = !result →
      PrefixEnsures (AtCounter origin replay record pkt result) (Safe origin replay) (f bad) Q) :
    PrefixEnsures (AtCounter origin replay record pkt result) (Safe origin replay)
      (liftPrefix (liftWG (branch .rxPollCounterInvalid !result)) >>= f) Q := by
  apply PrefixEnsures.bind (Q := fun bad h w => AtCounter origin replay record pkt result h w ∧ bad = !result)
  · apply PrefixEnsures.lift _ (fun _ _ hi => hi.1.2)
    intro h w bad v hi run
    cases run
    exact ⟨hi,rfl⟩
  · intro bad w h hi
    exact next bad hi.2 w h hi.1

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
