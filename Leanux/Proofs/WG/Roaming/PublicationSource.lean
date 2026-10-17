import Leanux.Proofs.WG.Roaming.PublicationModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.Basic

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original publication and held reference, before irqExit. The owner
comes from the actual embedded keypair word, not the packet's peer field. -/
def enqueuePublication (id : SkbId) (state : PacketState) :
    Leanux.M (PeerId × Campaign2.Product.Snapshot) := do
  let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
  peerGet pid
  let p ← getPeer pid
  if !(p.rxQueue.all.contains id) then
    invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => { q with state }
  setPeer pid { p with napiScheduled := true }
  return (pid, ← Campaign2.Product.read)

def publicationPublish (id : SkbId) (decrypted : Option RxPacket) :
    Leanux.M (PeerId × Campaign2.Product.Snapshot) := do
  if ← branch .decWorkerDecrypted decrypted.isSome then
    let some d := decrypted | invariant "unreachable"
    setRxSkb id fun _ => d
    enqueuePublication id .crypted
  else enqueuePublication id .dead

def publicationPacket (afterSoftirq : Campaign2.Product.Snapshot) (id : SkbId) :
    Leanux.M PublicationCut := do
  let input ← getRxSkb id
  let beforeDecrypt ← Campaign2.Product.read
  let decrypted ← decryptPacket input
  let published ← publicationPublish id decrypted
  return ⟨afterSoftirq, beforeDecrypt, id, published.1, input, decrypted, published.2⟩

def publicationSelected (after : Campaign2.Product.Snapshot) (id : SkbId)
    (ring : PtrRing SkbId) : Leanux.M PublicationCut := do
  _ ← branch .decWorkerConsumed true
  modifyDev fun d => { d with decryptQueue := ring }
  publicationPacket after id

/-- Executes the actual first callback and stops at publication, before the
original interrupt-exit callback. Snapshot reads change no execution state. -/
def publicationPrefix (softirq : Leanux.M Unit) : Leanux.M (Option PublicationCut) := do
  softirq
  let afterSoftirq ← Campaign2.Product.read
  match (← getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← branch .decWorkerConsumed false
    return none
  | (some id, ring) =>
    return some (← publicationSelected afterSoftirq id ring)

def publicationSuffix (softirq irqExit : Leanux.M Unit) (cut : Option PublicationCut) : Leanux.M Bool := do
  match cut with
  | none => pure false
  | some cut =>
    irqExit
    peerPut (some cut.owner)
    softirq
    pure true

theorem enqueuePerPeerRx_publication (irqExit : Leanux.M Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx irqExit id state = (do
      let published ← enqueuePublication id state
      irqExit
      peerPut (some published.1)) := by
  simp only [enqueuePerPeerRx, enqueuePublication, bind_assoc]
  congr 1
  funext pkt
  congr 1
  funext pid
  congr 1
  funext u
  congr 1
  funext p
  split <;> simp only [bind_assoc, pure_bind]
  all_goals rfl

theorem decryptStep_publication (softirq irqExit : Leanux.M Unit) :
    decryptStep softirq irqExit =
      (publicationPrefix softirq >>= publicationSuffix softirq irqExit) := by
  simp only [decryptStep, publicationPrefix, publicationSelected, publicationPacket, publicationPublish,
    enqueuePerPeerRx_publication, bind_assoc, pure_bind]
  congr 1
  funext u
  funext w
  change StateT.run _ w = StateT.run _ w
  simp only [StateT.run_bind]
  congr 1
  funext out
  rcases out with ⟨d, v⟩
  cases hc : d.decryptQueue.consume with
  | mk first ring =>
    cases first <;> simp only [StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
    all_goals try rfl
    congr 1
    funext consumed
    congr 1
    funext modified
    congr 1
    funext packet
    try simp only [Campaign2.Product.read, pure_bind, StateT.run_bind, StateT.run_pure]
    congr 1
    funext decrypted
    congr 1
    funext tested
    split <;> cases hd : decrypted.1 <;>
      simp only [bind_assoc, publicationSuffix, StateT.run_bind, StateT.run_pure]
    all_goals rfl

/-- Inspect the prefix from the same entry state, then execute the complete
original step. The second callback and reference release are not omitted. -/
def observedDecryptStep (softirq irqExit : Leanux.M Unit) :
    Leanux.M (Bool × Campaign2.Product.Outcome (Option PublicationCut)) := do
  let observation ← Campaign2.Product.inspect (publicationPrefix softirq)
  let consumed ← decryptStep softirq irqExit
  pure (consumed, observation)

theorem observedDecryptStep_erase (softirq irqExit : Leanux.M Unit) :
    (do let result ← observedDecryptStep softirq irqExit; pure result.1) =
      decryptStep softirq irqExit := by
  funext w
  change (((decryptStep softirq irqExit).run w >>= fun out =>
    Except.ok ((out.1, Campaign2.Product.observeResult ((publicationPrefix softirq).run w)), out.2))
      >>= fun out => Except.ok (out.1.1, out.2)) = (decryptStep softirq irqExit).run w
  cases h : (decryptStep softirq irqExit).run w with
  | error e => rfl
  | ok pair => rfl

end Leanux.Proofs.WG.Roaming
