import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteClaims
import Leanux.Proofs.WG.Roaming.ReceiveStepSetterEffects
import Leanux.Proofs.WG.Roaming.RemoteChronologyCaptureSource
import Leanux.Proofs.WG.Roaming.RemoteChronologyClassificationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG

theorem receiveStep_setter (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (liftWG receiveStep) (fun s => s = entry)
      (fun value final => ∃ q : Observation,
        q.Valid ∧ q.entry = entry ∧ q.finish = final ∧ q.value = value ∧ q.Facts ∧
        RemoteRetained (setterMap (remoteMap entry.toSnapshot) q.setter)
          (remoteMap final.toSnapshot) ∧
        ∀ pid remote, q.setter = some (pid,remote) → q.Cause pid remote) := by
  intro w value v pre run
  obtain ⟨q,valid,start,finish,result,facts⟩ := receiveStep_observation entry w value v pre run
  refine ⟨q,valid,start,finish,result,facts,?_,observation_setter_authenticated q facts⟩
  rw [← start,← finish]
  exact observation_setter_effect q facts

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
