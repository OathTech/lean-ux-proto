import Leanux.Proofs.WG.Queues.HandshakeSlots
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Origins.OwnerHandshake

/-! The existing owner journal supplies the concrete handshake entry facts.
The optional acquisition result keeps its source-owned loan while this same
normal run transports configured/current support and all three nullable slots. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def Entry (w : WGWorld) : Prop :=
  (∃ history, CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w) ∧ CurrentSlots.Inv w

theorem of_owner (owner : OwnerChecks.Inv history w) (slots : CurrentSlots.Inv w.wg) : Entry w.wg :=
  ⟨⟨Origins.HistorySupport.sessions history,owner.current.2.1,owner.carrier⟩,slots⟩

theorem entry_facts (hi : Entry w) :
    ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w ∧ CurrentSlots.Inv w := by
  obtain ⟨⟨history,current,carrier⟩,slots⟩ := hi
  exact ⟨current.1,carrier,slots⟩

private theorem combine (action : WG.M α)
    (support : Preserves (fun w => ∃ history,CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w) action)
    (slots : Preserves CurrentSlots.Inv action) : Preserves Entry action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp support w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots w a x v b hi.2 run⟩

theorem initiation (msg : List UInt8) : Preserves Entry (consumeInitiation msg) :=
  combine _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.initiation) msg)
    (HandshakeSlots.consumeInitiation msg)

theorem response (msg : List UInt8) : Preserves Entry (consumeResponse msg) :=
  combine _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.response) msg)
    (HandshakeSlots.consumeResponse msg)

theorem cookie (msg : List UInt8) : Preserves Entry (cookieMessageConsume msg) :=
  combine _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.consumeCookie) msg)
    (HandshakeSlots.cookieMessageConsume msg)

/-- None has paid any source acquisition; Some retains exactly its attributed
loan. Both claims concern the actual same native receipt and Ambient cuts. -/
theorem initiation_funded (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (entry : Entry w) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((result,v),b)) :
    HandshakeLoans.FundedResult holders cs loans result v ∧ Entry v :=
  ⟨HandshakeLoans.consumeInitiation_funded msg hi stable a b run,
    (hoare_iff_run_ambient _ _ _).mp (initiation msg) w a result v b entry run⟩

theorem response_funded (msg : List UInt8) {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (entry : Entry w) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a = .ok ((result,v),b)) :
    HandshakeLoans.FundedResult holders cs loans result v ∧ Entry v :=
  ⟨HandshakeLoans.consumeResponse_funded msg hi stable a b run,
    (hoare_iff_run_ambient _ _ _).mp (response msg) w a result v b entry run⟩

private theorem endpoint_slots (pid : PeerId) (src : SkbSource) :
    Preserves CurrentSlots.Inv (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact CurrentSlots.view_preserves (project := id) (Affiliation.kernel (project := id)
         (endpointFromSkb_sameWGStore _)))
    | (rx_retention_head setPeerEndpoint
       exact CurrentSlots.fields_preserves (project := id)
         ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) _ _))
    | slot_traffic_step

theorem endpoint (pid : PeerId) (src : SkbSource) : Preserves Entry (setPeerEndpointFromSkb pid src) :=
  combine _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.endpoint) pid src)
    (endpoint_slots pid src)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry
