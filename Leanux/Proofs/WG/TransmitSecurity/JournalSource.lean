import Leanux.Proofs.WG.TransmitSecurity.DriverOuterProjection
import Leanux.Proofs.WG.TransmitSecurity.NativeAdapter
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.Logged.NativeCapture

/-! One retained journal for native reservation, packet allocation, encryption
ring selection, actual AEAD, queue publication and TX disposal. Hooks are placed
in the shared initialized driver, so their order is an execution order. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets

inductive Event where
  | nonce (value : Nonce.Allocation)
  | reserved (slot : KeypairId) (run : WGRunWitness Nat)
  | allocated (packets : List DataPacket) (run : WGRunWitness (List SkbId))
  | routed (family addr : Nat) (packets : List Packet) (mtu : Nat) (run : WGRunWitness (Except Int PeerId))
  | ring (value : TxRing.Event)
  | polled (run : RunWitness (Option (List SkbId)))
  | encrypted (value : WorkerEncryption.Receipt)
  | encryptionReturn (item : Option (List SkbId)) (run : RunWitness Bool)
  | disposition (value : TxDisposition.Event)

def nonce? : Event → Option Nonce.Allocation | .nonce value => some value | _ => none

def encryption? : Event → Option WorkerEncryption.Receipt | .encrypted value => some value | _ => none

def disposition? : Event → Option TxDisposition.Event | .disposition value => some value | _ => none

def ring? : Event → Option TxRing.Event
  | .ring value => some value
  | .disposition (.ring value) => some value
  | _ => none

def reserve (slot : KeypairId) : WGPrefix Event Nat :=
  receiptWGObserved (focusStatePrefix Event.nonce nonce? (Nonce.reserveObserved slot)) (.reserved slot)

def allocate (packets : List DataPacket) : WGPrefix Event (List SkbId) :=
  receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb)) (.allocated packets)

def create (pid : PeerId) (item : List SkbId) : WGPrefix Event Unit :=
  NativeAdapter.lower (focusPrefix Event.disposition disposition? (TxDisposition.create pid item))

def front (family addr : Nat) (packets : List Packet) (mtu : Nat) : WGPrefix Event (Except Int PeerId) :=
  receiptWGObserved (liftWGPrefix (txFront family addr packets mtu)) (.routed family addr packets mtu)

def poll : PrefixM Event (Option (List SkbId)) :=
  receiptObserved (focusPrefix Event.ring ring? TxRing.poll) Event.polled

def encrypt (item : Option (List SkbId)) : PrefixM Event Bool :=
  receiptObserved (focusPrefix Event.encrypted encryption? (WorkerEncryption.tail item)) (.encryptionReturn item)

def transmit (pid : PeerId) : PrefixM Event Bool :=
  focusPrefix Event.disposition disposition? (TxDisposition.step pid)

def hooks : Driver.Hooks Event where
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.Journal
