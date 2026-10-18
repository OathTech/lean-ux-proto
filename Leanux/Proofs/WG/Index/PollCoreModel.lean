import Leanux.Proofs.WG.Index.ReceiveCoreSource
import Leanux.Proofs.WG.Noise.DriverTagPollSource
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.RetirementRetentionClaims
import Leanux.Proofs.WG.Index.TxDisposalCoreSource
import Leanux.Proofs.WG.Index.TransmitCoreSource
import Leanux.Proofs.WG.Index.IncomingIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def Absent (pid : PeerId) (w : WGWorld) : Prop :=
  responseTagMap w.dev pid = none

def Loop (pid : PeerId) (w : WGWorld) : Prop :=
  TimerCore.Ready w ∨ Absent pid w

def keyCell (w : WGWorld) (kid : KeypairId) :=
  (w.dev.bind fun d=>d.keypairs[kid]?).map (fun k=>(k.peer,k.refcount))

end Leanux.Proofs.WG.Index.PollCore
