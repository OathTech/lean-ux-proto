import Leanux.Proofs.WG.Config.KeyCollision
import Leanux.Proofs.WG.Config.QueuedRemoveModel

/-! Data-only effects of a completed private-key stage. Removal effects describe
the configured boundary; queued drains may also change resident stores. The
ordered installation relation uses the actual post-removal baseline. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG
inductive LookupEffect (before : Device) (pub : Key) : Device → Prop
  | absent (missing : before.peerHashtable.find? (·.1 == pub)=none) :
      LookupEffect before pub before
  | removed (pid : PeerId) (peer : Peer) (after : Device)
      (found : before.peerHashtable.find? (·.1 == pub)=some (pub,pid))
      (resident : before.peers[pid]?=some peer) (positive : 0<peer.refcount)
      (effect : QueuedRemove.Effect before pid after) :
      LookupEffect before pub after

def GeneratedEffect (before : Device) (key : Key) (after : Device) : Prop :=
  ((publicResult key).2=false ∧ after=before) ∨
  ∃ pub,publicResult key=(some pub,true) ∧ LookupEffect before pub after

inductive Effect (attrs : DeviceAttrs) (before : Device) : Device → Prop
  | absent (none : attrs.privateKey=Option.none) : Effect attrs before before
  | unchanged (key : Key) (some : attrs.privateKey=Option.some key)
      (same : before.staticIdentity.staticPrivate=key) : Effect attrs before before
  | changed (key : Key) (some : attrs.privateKey=Option.some key)
      (different : before.staticIdentity.staticPrivate≠key) (baseline after : Device)
      (generated : GeneratedEffect before key baseline)
      (observations : List (Option (Int64 × Option Bool)))
      (installed : ObservedKeyPeerRun (requestsStagedSend baseline key)
        (installedDevice baseline key) baseline.peerList observations after) :
      Effect attrs before after


end Leanux.Proofs.WG.Config.KeyStage
