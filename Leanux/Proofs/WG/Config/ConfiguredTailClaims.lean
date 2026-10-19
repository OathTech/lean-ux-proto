import Leanux.Proofs.WG.Config.ConfiguredTailSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- Normal creation preserves all represented configured owners. A successful
allocation additionally publishes its actual selected slot in the base list;
allocation refusal is included and no output representation is assumed. -/
theorem original_create (key : Key) (psk : Option Key) :
    Campaign2.Ensures (peerCreate key psk) ProjectedReady (fun result s =>
      ProjectedReady s ∧ ∀ pid,result=.ok pid →
        ∃ d,s.wg.device=some d ∧ pid∈d.peerList) := by
  intro g a result v b pre run
  obtain ⟨post,selected⟩ := create_ready key psk g a result v b pre run
  refine ⟨post,?_⟩
  intro pid equal
  obtain ⟨d,device,_⟩ := post
  exact ⟨d,device,by simpa only [BaseCoherence.slots,device,Option.map_some,Option.getD_some]
    using (selected pid equal)⟩

/-- Replacing one selected peer's allowed IPs keeps represented route owners
configured. The original normal run supplies its resident target. -/
theorem original_removeByPeer (pid : PeerId) :
    Campaign2.Ensures (removeByPeer pid) ProjectedReady (fun _=>ProjectedReady) := by
  intro g a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (removeByPeer_ready pid) g a result v b pre run

/-- The original mixed allowed-IP/keepalive/staged-send tail retains configured
route ownership and pays the real caller loan on every normal return. -/
theorem original_tail (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (shape : PeerAddressShape attrs) :
    Campaign2.Ensures (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (ProjectedSelected cs (paid::loans) paid.slot)
      (fun _=>ProjectedEntry cs loans) := by
  intro g a result v b pre run
  apply (entry_snapshot cs loans v b).mpr
  exact (hoare_iff_run_ambient _ _ _).mp (tail_entry cs loans paid attrs shape)
    g a result v b ((selected_snapshot cs (paid::loans) paid.slot g a).mp pre) run

end Leanux.Proofs.WG.Config.OwnerConfiguration
