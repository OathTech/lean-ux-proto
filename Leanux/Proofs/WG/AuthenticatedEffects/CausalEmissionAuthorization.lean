import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.CausalRootsSockets

/-! Positional native append receipts inherit their own initialized cause.
The cookie exception is the native under-load/MAC1 path; repeated equal-valued
datagrams are never reassigned to an older receipt by value membership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def AuthorizedAppend (before : List Event) : Event → Prop
  | .old (.socket receipt) =>
      Roots.Rooted before ∧ receipt.Valid ∧
        SocketEmission receipt.endpoint receipt.packet.value.bytes receipt.packet.value.ds
          receipt.socket.before.wg.sent receipt.socket.after.wg.sent
  | .protocolSocket receipt =>
      Roots.Rooted before ∧ receipt.Valid ∧ receipt.cause = CausalScope.current scope? before ∧
        SocketEmission receipt.args.endpoint receipt.args.bytes receipt.args.ds
          receipt.run.before.sent receipt.run.after.sent
  | .cookieSocket receipt =>
      receipt.Valid ∧ receipt.Qualifying ∧
        (messageType receipt.input = MESSAGE_HANDSHAKE_INITIATION ∨
          messageType receipt.input = MESSAGE_HANDSHAKE_RESPONSE)
  | _ => False

private theorem contributing (event : Event) (index : Nat) (datagram : SentDatagram)
    (atPosition : (added event)[index]? = some datagram) :
    (∃ receipt, event = .old (.socket receipt)) ∨
      (∃ receipt, event = .protocolSocket receipt) ∨ (∃ receipt, event = .cookieSocket receipt) := by
  cases event <;> try (simp only [added,List.getElem?_nil] at atPosition; contradiction)
  case old value =>
    cases value <;> try (simp only [added,List.getElem?_nil] at atPosition; contradiction)
    exact Or.inl ⟨_,rfl⟩
  case protocolSocket receipt => exact Or.inr (Or.inl ⟨receipt,rfl⟩)
  case cookieSocket receipt => exact Or.inr (Or.inr ⟨receipt,rfl⟩)

theorem initialized_append (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after)
    (index : Nat) (datagram : SentDatagram) (atPosition : (added event)[index]? = some datagram) :
    AuthorizedAppend before event := by
  rcases contributing event index datagram atPosition with ⟨receipt,rfl⟩ | ⟨receipt,rfl⟩ | ⟨receipt,rfl⟩
  · exact Roots.socket trace placeholders before after receipt position
  · exact Roots.protocol_socket trace placeholders before after receipt position
  · exact Receipts.initialized_cookie_qualified trace placeholders before after receipt position

/-- A particular append ordinal is backed by its own native socket occurrence
and that occurrence's finite causal root or qualified cookie exception. -/
theorem initialized_stream (trace : Runner.Trace) (placeholders : Bool)
    (ordinal : Nat) (datagram : SentDatagram)
    (atPosition : (emitted (runPrefixOuter (execute trace placeholders) []).2)[ordinal]? = some datagram) :
    ∃ before event after inside,
      (runPrefixOuter (execute trace placeholders) []).2 = before ++ event :: after ∧
      (added event)[inside]? = some datagram ∧
      ordinal = (emitted before).length + inside ∧ AuthorizedAppend before event := by
  obtain ⟨before,event,after,inside,position,member,order⟩ := locate _ ordinal datagram atPosition
  exact ⟨before,event,after,inside,position,member,order,
    initialized_append trace placeholders before after event position inside datagram member⟩

/-- Each actual pre-delivery sent position comes from an exact strictly earlier
native append with its own cause, including when delivery or a later caller Stops. -/
theorem initialized_delivery (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (sent : List SentDatagram)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = before ++ .delivery sent :: after)
    (index : Nat) (datagram : SentDatagram) (atPosition : sent[index]? = some datagram) :
    ∃ receiptBefore event receiptAfter inside,
      before = receiptBefore ++ event :: receiptAfter ∧
      (added event)[inside]? = some datagram ∧
      (emitted before).length - sent.length + index = (emitted receiptBefore).length + inside ∧
      AuthorizedAppend receiptBefore event := by
  obtain ⟨pre,event,post,inside,earlier,member,order⟩ :=
    Deliveries.initialized_occurrence trace placeholders before after sent position index datagram atPosition
  have whole : (runPrefixOuter (execute trace placeholders) []).2 =
      pre ++ event :: (post ++ .delivery sent :: after) := by
    simp only [position,earlier,List.append_assoc,List.cons_append]
  exact ⟨pre,event,post,inside,earlier,member,order,
    initialized_append trace placeholders pre _ event whole inside datagram member⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
