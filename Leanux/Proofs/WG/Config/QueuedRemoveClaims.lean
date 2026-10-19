import Leanux.Proofs.WG.Config.QueuedRemoveSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.QueuedRemove
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

/-- Whole-command normal endpoint, stated over the campaign projection.
There are no empty-queue, successful-callback or post-state premises. -/
theorem original_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key) (flagattr : attrs.flags=some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>ret=0 ∧ ProjectedEntry cs loans s ∧
        ∃ after,s.wg.device=some after ∧ Effect before pid after) := by
  intro g a result v b pre run
  obtain ⟨zero,entry,after,present,effect⟩ :=
    command cs loans attrs key flags pid before pubkey flagattr valid protocol remove found
      g a result v b ⟨(entry_snapshot cs loans g a).mp pre.1,pre.2⟩ run
  exact ⟨zero,(entry_snapshot cs loans v b).mpr entry,after,present,effect⟩


end Leanux.Proofs.WG.Config.QueuedRemove
