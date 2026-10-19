import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEntrySource

/-! Concrete completed exchange and cookie-consumer entries. The format laws
are definitional; the initialized carrier has no abstract event-law premise. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive EntryEvent where
  | exchange (event : Exchange.Event)
  | cookie (receipt : CookieEntry)

def EntryEvent.before : EntryEvent → WGWorld
  | .exchange event => event.before
  | .cookie receipt => receipt.run.before

def EntryEvent.Valid : EntryEvent → Prop
  | .exchange event => event.Valid
  | .cookie receipt => receipt.run.Valid (cookieMessageConsume receipt.input)

instance concreteEntryFormat : EntryFormat EntryEvent where
  before := EntryEvent.before
  valid := EntryEvent.Valid
  exchange := EntryEvent.exchange
  exchange_before := fun _ => rfl
  exchange_valid := fun _ h => h
  cookie := some EntryEvent.cookie
  cookie_before := by
    intro record same receipt
    cases Option.some.inj same
    rfl
  cookie_valid := by
    intro record same receipt valid
    cases Option.some.inj same
    exact valid

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
