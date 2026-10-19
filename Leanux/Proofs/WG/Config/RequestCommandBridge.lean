import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge
import Leanux.Proofs.WG.Config.CommandOrderInspectionBridge

/-! Nested command inspections tied to the same original native witness as a completed outer peer receipt. No extra request observer is defined. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise

def PeerCommandMatches (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection) : Prop :=
  ∃native : WGRunWitness Int, native.Valid (setPeerCmd p) ∧
    receipt (.peer p) native=r ∧
    CommandOrder.inspection p native.before native.ambientBefore=nested

def PeerCommandFacts (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection) : Prop :=
  PeerCommandMatches r p nested ∧ nested.outcome=.ok (r.result,r.after) ∧
    CommandOrder.Facts p r.before nested

def NestedCommands (attrs : DeviceAttrs) (result : Inspection) : Prop :=
  ∀(i : Nat) (r : Receipt) (p : PeerAttrs),(peerReceipts result.receipts)[i]?=some r → r.kind=.peer p →
    (attrs.peers.getD [])[i]?=some (.attrs p) ∧
      ∃nested,PeerCommandFacts r p nested

end Leanux.Proofs.WG.Config.RequestOrder
