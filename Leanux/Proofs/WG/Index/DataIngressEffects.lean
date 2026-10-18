import Leanux.Proofs.WG.Index.OwnerReferenceFrames
import Leanux.Proofs.WG.Index.ConfigurationIndexFrames
import Leanux.Proofs.WG.Index.LookupRetirementClaims
import Leanux.Proofs.WG.Queues.RxIngressCarrier

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem key_acquire_core (d : Device) (kid : KeypairId) (key : Keypair)
    (resident : d.keypairs[kid]?=some key) (pre : DeviceIndexCore d) :
    DeviceIndexCore (Config.withKeypair d kid {key with refcount:=key.refcount+1}) := by
  have words (other : KeypairId) :
      (Config.withKeypair d kid {key with refcount:=key.refcount+1}).keypairs[other]?.map Keypair.peer =
        d.keypairs[other]?.map Keypair.peer := by
    by_cases same : kid=other
    · subst other; simp [Config.withKeypair,resident]
    · simp [Config.withKeypair,Std.TreeMap.getElem?_insert,same]
  refine ⟨pre.1,hashSlotCoverage_transport d _ rfl (fun _=>rfl) words pre.2.1,
    keypairAcquire_owner_coherent d kid key resident pre.2.2.1,?_⟩
  apply deadHashedReserved_transport [] d (Config.withKeypair d kid {key with refcount:=key.refcount+1}) rfl (fun _ h=>h) _ (fun _ p h=>⟨p,h,rfl,rfl⟩) pre.2.2.2
  intro entry _ other owner
  simpa only [owner,ownerWord] using words other

end Leanux.Proofs.WG.Index.DataIngress
