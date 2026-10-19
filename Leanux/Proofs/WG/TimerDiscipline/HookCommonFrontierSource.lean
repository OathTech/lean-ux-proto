import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierBridge
import Leanux.Proofs.WG.TimerDiscipline.HookNapiCommonSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open HandshakeJournal
theorem transmit_frontier (pid : PeerId) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (transmit pid) :=
  focus_frontier _ _ (HookJournal.TransmitWorker.iteration_erases pid)
    (product_ordinary_counter (Keypairs.EnvFrames.txIter_ordinary pid _
      (Keypairs.SameView.ordinary (Keypairs.EnvFrames.condResched_sameSnapshot _))))
theorem receive_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered receive :=
  HandshakeJournal.step_frontier.liftWGObserver.preserves
theorem sendOne_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered sendOne :=
  focus_frontier _ _ HookJournal.SendEnvironment.one_erases
    (product_snapshot_counter Keypairs.EnvFrames.runOneSendWorker_sameSnapshot)
theorem consume_frontier (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (consume pid pkt ep) :=
  observer_frontier _ _ (consume_appends pid pkt ep) (consume_erases pid pkt ep)
    (StateHistoryFrame.liftWGObserver (fun g=>
      focusPrefix_other _ _ _ (fun _=>rfl) ((ReceiveHookJournal.consume pid pkt ep).run g)))
    (counter_product (ordinary_counter (Keypairs.WGMore.consumeDataDone_ordinary pid pkt ep)))
theorem stack_frontier (packets : List (List UInt8)) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (stack packets) :=
  quiet_frontier _ (product_ordinary_counter
    (Keypairs.ordinary_forM packets Env.deliverInner Keypairs.EnvFrames.deliverInner_ordinary))
end Leanux.Proofs.WG.TimerDiscipline.HookCommon
