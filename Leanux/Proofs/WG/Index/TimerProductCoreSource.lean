import Leanux.Proofs.WG.Index.TimerProductCoreFrames
import Leanux.Proofs.WG.Index.TimerProductRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem timerSection (worker : Worker) (body : Leanux.M Unit)
    (keep : Preserves (fun w : World=>Ready w.wg) body) :
    Preserves (fun w : World=>Ready w.wg) (Env.runTimerSection worker body) :=
  TimerDiscipline.runTimerSection_kernel_contract worker body
    (fun wg _ _ _=>Ready wg) (fun wg _ _ _=>Ready wg) keep

theorem dispatch_ready (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (wheel : WheelEntry) (prior : Option UInt64) :
    Preserves (fun w : World=>Ready w.wg) (timerDispatchUnit worker pid timer wheel prior) :=
  TimerProductRules.dispatch _ (fun {_}=>product_store) timerSection
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (callback p t)))
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (del p t)))
    worker pid timer wheel prior

theorem placeholder_ready (j : UInt64) :
    Preserves (fun w : World=>Ready w.wg) (RxHistory.placeholderTimerPassSource j) :=
  TimerProductRules.placeholder _ (fun {_}=>product_store) timerSection
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (callback p t)))
    (fun p t=>PublicationPoll.native_product _ _ ((ensures_iff _ _ _).mp (del p t))) j

end Leanux.Proofs.WG.Index.TimerCore
