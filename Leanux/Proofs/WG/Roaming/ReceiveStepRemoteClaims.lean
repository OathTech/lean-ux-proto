import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Std.Do

theorem receiveStep_observation (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (liftWG receiveStep) (fun s => s = entry)
      (fun value final => ∃ q : Observation,
        q.Valid ∧ q.entry = entry ∧ q.finish = final ∧ q.value = value ∧ q.Facts) := by
  intro w value v pre run
  obtain ⟨q,matched,facts⟩ := complete ⟨value,w,v⟩ run
  exact ⟨q,⟨⟨value,w,v⟩,run,matched⟩,matched.1.trans pre,
    matched.2.1,matched.2.2.1,facts⟩

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
