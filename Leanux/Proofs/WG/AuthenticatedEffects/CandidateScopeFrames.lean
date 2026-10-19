import Leanux.Proofs.WG.AuthenticatedEffects.CandidatePollCarrier

/-! Concrete scope markers preserve the selected packet and the actual RX
authentication carrier. These frames discharge the candidate poll's marker
obligations without declaring the candidate accepted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E Cause : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay}

private theorem marker_inv {h : List E} {w : World} (hi : Inv origin replay h w)
    (event : E) (ho : origin event = none) (hr : replay event = none) :
    Inv origin replay (h ++ [event]) w := by
  refine ⟨?_,hi.2.quiet (by simp only [List.filterMap_cons,List.filterMap_nil,hr])⟩
  simpa only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,ho,List.append_nil] using hi.1

theorem scope_enter_inv (record : CausalScope.Event Cause → E) (cause : Cause)
    (ho : ∀ event, origin (record event) = none) (hr : ∀ event, replay (record event) = none) :
    Preserves (origin := origin) (replay := replay) (CausalScope.enterPrefix record cause) := by
  intro w h hi
  have kept := marker_inv hi (record (.entered ⟨h.length,cause⟩)) (ho _) (hr _)
  exact ⟨[record (.entered ⟨h.length,cause⟩)],rfl,kept.2,kept⟩

theorem scope_enter_picked (record : CausalScope.Event Cause → E) (cause : Cause)
    (ho : ∀ event, origin (record event) = none) (hr : ∀ event, replay (record event) = none)
    (skb : SkbId) (pkt : RxPacket) :
    PrefixPreserves (Picked origin replay skb pkt) (Safe origin replay)
      (CausalScope.enterPrefix record cause) := by
  intro w h hi
  have kept := marker_inv hi.1 (record (.entered ⟨h.length,cause⟩)) (ho _) (hr _)
  exact ⟨[record (.entered ⟨h.length,cause⟩)],rfl,kept.2,kept,hi.2⟩

theorem scope_leave_inv (record : CausalScope.Event Cause → E) (position : Nat)
    (ho : ∀ event, origin (record event) = none) (hr : ∀ event, replay (record event) = none) :
    Preserves (origin := origin) (replay := replay) (CausalScope.leavePrefix record position) := by
  intro w h hi
  have kept := marker_inv hi (record (.exited position)) (ho _) (hr _)
  exact ⟨[record (.exited position)],rfl,kept.2,kept⟩

theorem scoped_poll_checked (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (scopeRecord : CausalScope.Event Cause → E) (candidate : SkbId → RxPacket → Cause)
    (scopeOrigin : ∀ event, origin (scopeRecord event) = none)
    (scopeReplay : ∀ event, replay (scopeRecord event) = none)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (hc : ∀ pid pkt ep, Preserves (origin := origin) (replay := replay) (consume pid pkt ep))
    (hr : ∀ gro bytes, Preserves (origin := origin) (replay := replay) (receive gro bytes))
    (hf : ∀ gro, Preserves (origin := origin) (replay := replay) (flush gro))
    (pid : PeerId) (budget : Nat) :
    Preserves (origin := origin) (replay := replay)
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a))
        (fun skb pkt => CausalScope.enterPrefix scopeRecord (candidate skb pkt))
        (CausalScope.leavePrefix scopeRecord) (TransportDriver.counter record)
        consume receive flush pid budget) :=
  candidate_poll_checked origin replay record inverse quiet _ _ consume receive flush
    (fun skb pkt => scope_enter_picked scopeRecord (candidate skb pkt) scopeOrigin scopeReplay skb pkt)
    (fun position => scope_leave_inv scopeRecord position scopeOrigin scopeReplay)
    hc hr hf pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
