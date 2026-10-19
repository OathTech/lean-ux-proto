import Leanux.Proofs.WG.Config.ScalarTailSource
import Leanux.Proofs.WG.Index.ConfigurationCoreBridge

/-! Projected normal-return contracts. PSK and the full source-defined Endpoint persist even on an allowed-IP errno; the interval changes exactly on the nonnegative finish path. No final survival or empty-work assumption. REMOVE_ME is separately covered and is explicitly excluded here. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarTail
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

theorem original_tail (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (expected : Cell) :
    Campaign2.Ensures (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (FinishInput cs loans paid expected)
      (fun result s=>Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (tailCell attrs result expected)) := by
  intro g a result final b pre run
  have effect := tail_exact cs loans paid attrs expected g a result final b
    ⟨(Index.configurationInput_snapshot cs (paid::loans) g a).mp pre.1,pre.2⟩ run
  exact ⟨(Index.configurationInput_snapshot cs loans final b).mpr effect.1,effect.2⟩

theorem original_update (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (keep : flags &&& WGPEER_F_REMOVE_ME=0)
    (d : Device) (p : Peer) (resident : d.peers[paid.slot]?=some p)
    (member : paid.slot∈d.peerList) :
    Campaign2.Ensures (Configuration.peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun s=>Index.View.ConfigurationInput cs (paid::loans) s ∧ s.wg.device=some d)
      (fun result s=>Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (tailCell attrs result (prefixCell p psk attrs.endpoint))) := by
  intro g a result final b pre run
  have effect:=update_exact cs loans paid attrs flags psk keep d p resident member g a result final b
    ⟨(Index.configurationInput_snapshot cs (paid::loans) g a).mp pre.1,pre.2⟩ run
  exact ⟨(Index.configurationInput_snapshot cs loans final b).mpr effect.1,effect.2⟩

end Leanux.Proofs.WG.Config.ScalarTail
