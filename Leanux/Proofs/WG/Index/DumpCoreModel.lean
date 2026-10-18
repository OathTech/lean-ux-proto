import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.StagingRichFrames
import Leanux.Proofs.WG.Index.StagingIndexEffects
import Leanux.Proofs.WG.Config.DumpInvariantSource
import Leanux.Proofs.WG.Index.ConfigurationDeviceSource
import Leanux.Proofs.WG.Index.RetirementReleaseSource
import Leanux.Proofs.WG.Queues.HolderDumpEntry
import Leanux.Proofs.WG.Index.LifecycleEnvironmentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

def DeviceFrame (before after : Option Device) : Prop :=
  StagingRich.Frame {dev:=before} {dev:=after}

def HandshakeCoherent (d : Device) : Prop :=
  ∀ e ∈ d.indexTable, ∀ pid, e.owner=.handshake pid →
    ∃ p,d.peers[pid]?=some p ∧ p.handshakeEntryPeer=some pid ∧ 0<p.refcount

def Shape (present : Bool) (w : WGWorld) : Prop :=
  w.dev.isSome=present ∧ ∀d,w.dev=some d → HandshakeCoherent d

def Essentials (w : WGWorld) : Prop :=
  BaseCoherence.Inv w ∧ ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w

end Leanux.Proofs.WG.Index.DumpCore
