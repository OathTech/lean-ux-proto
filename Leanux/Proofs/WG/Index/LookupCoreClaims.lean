import Leanux.Proofs.WG.Index.LookupCoreModel
import Leanux.Proofs.WG.Index.LookupCoreEffects
import Leanux.Proofs.WG.Index.IncomingIndexFrames
import Leanux.Proofs.WG.Index.PeerReleaseTableFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do

/-- The actual public-key lookup preserves Core on every normal result and
supplies its selected peer and strictly nonfinal reference on success.
Missing, zero-count and overflow cases retain the original behavior. -/
theorem pubkeyLookup_indexCore_held (key : Key) :
    Campaign2.Ensures (pubkeyLookup key) View.IndexCore
      (fun result s => View.IndexCore s ∧
        ∀ pid, result=some pid → View.IndexCoreHeld pid s) := by
  intro w a result v b pre run
  have post := pubkeyLookup_preserves_acquire_source key DeviceIndexCore
    deviceIndexCore_acquire w a result v b pre run
  exact ⟨post.1,fun pid returned => ⟨post.1,post.2 pid returned⟩⟩

/-- Paying this still-held reference is nonfinal. The contract is appropriate
at an actual acquisition/rejection cut; it does not assert that arbitrary
intervening calls preserve the reference budget. -/
theorem peerPut_indexCore_held (pid : PeerId) :
    Campaign2.Ensures (peerPut (some pid)) (View.IndexCoreHeld pid)
      (fun _ => View.IndexCore) := by
  intro w a result v b pre run
  have tables := (ensures_iff _ _ _).mpr (peerPut_tables (some pid))
    w a result v b (fun d device => (pre.1 d device).1) run
  have retained := peerPut_incomingIndexHeld [] pid w a result v b
    ⟨fun d device => ⟨(pre.1 d device).2.1,(pre.1 d device).2.2.2⟩,pre.2⟩ run
  have owners := peerPut_ownerHeld pid w a result v b
    ⟨fun d device => (pre.1 d device).2.2.1,pre.2⟩ run
  exact fun d device => ⟨tables d device,(retained d device).1,
    owners d device,(retained d device).2⟩
end Leanux.Proofs.WG.Index
