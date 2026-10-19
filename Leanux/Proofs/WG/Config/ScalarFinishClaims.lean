import Leanux.Proofs.WG.Config.ScalarFinishSource
import Leanux.Proofs.WG.Index.ConfigurationCoreBridge

/-! Normal acquired finish completion retains the selected incarnation, PSK and full Endpoint; the optional keepalive value is written exactly. Original refusals and Stops remain: this is not a total-return claim or a whole peer-command theorem. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarFinish
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention

theorem original_finish (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) (expected : Cell) :
    Campaign2.Ensures (Configuration.peerTailFinishSource attrs (some paid.slot) paid.slot ret)
      (FinishInput cs loans paid expected)
      (fun result s=>result=ret ∧ Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (finishCell attrs expected)) := by
  intro g a result final b pre run
  have effect := finish_exact cs loans paid attrs ret expected g a result final b
    ⟨(Index.configurationInput_snapshot cs (paid::loans) g a).mp pre.1,pre.2⟩ run
  exact ⟨effect.1,(Index.configurationInput_snapshot cs loans final b).mpr effect.2.1,effect.2.2⟩

end Leanux.Proofs.WG.Config.ScalarFinish
