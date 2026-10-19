import Leanux.Proofs.WG.TimerDiscipline.HandshakeFocusSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeJournal
abbrev Obs := PrefixM Event

def transmit (pid : PeerId) : Obs IterResult :=
  focusPrefix Event.hook decodeHook (HookJournal.TransmitWorker.iteration pid)
def receive : Obs Bool := liftWGObserver HandshakeJournal.step
def sendOne : Obs Unit :=
  focusPrefix Event.hook decodeHook HookJournal.SendEnvironment.one
def consume (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) : Obs (Option (List UInt8)) :=
  liftWGObserver (focusStatePrefix Event.hook decodeHook (ReceiveHookJournal.consume pid pkt ep))
def stack (packets : List (List UInt8)) : Obs Unit :=
  liftPrefix (packets.forM Env.deliverInner)

theorem transmit_erases (pid : PeerId) :
    ErasesPrefix (transmit pid) (txIter pid (Env.condResched .txWorker)) :=
  focusPrefix_erases _ _ (HookJournal.TransmitWorker.iteration_erases pid)
theorem receive_erases : ErasesPrefix receive (liftWG WG.receiveStep) :=
  liftWGObserver_erases HandshakeJournal.step_erases
theorem sendOne_erases : ErasesPrefix sendOne Env.runOneSendWorker :=
  focusPrefix_erases _ _ HookJournal.SendEnvironment.one_erases
theorem consume_erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesPrefix (consume pid pkt ep) (liftWG (consumeDataDone pid pkt ep)) :=
  liftWGObserver_erases (focusStatePrefix_erases _ _ (ReceiveHookJournal.consume_erases pid pkt ep))
theorem stack_erases (packets : List (List UInt8)) :
    ErasesPrefix (stack packets) (packets.forM Env.deliverInner) :=
  erasesPrefix_lift _

theorem transmit_valid (pid : PeerId) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (transmit pid) :=
  focus_valid (HookJournal.TransmitWorker.iteration_preserves pid)
theorem receive_valid :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory receive :=
  HandshakeJournal.step_valid.liftWGObserver.preserves
theorem sendOne_valid :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory sendOne :=
  focus_valid HookJournal.SendEnvironment.one_preserves
theorem consume_valid (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (consume pid pkt ep) :=
  (focus_native_valid (ReceiveHookJournal.consume_valid pid pkt ep)).liftWGObserver.preserves

theorem transmit_paired (pid : PeerId) :
    PrefixPreserves (fun h _=>Paired h) Paired (transmit pid) :=
  focus_paired (HookJournal.TransmitWorker.iteration_appends pid)
    (HookJournal.transmit_iteration_derived_frame pid)
theorem receive_paired : PrefixPreserves (fun h _=>Paired h) Paired receive :=
  HandshakeJournal.step_paired.liftWGObserver.preserves
theorem sendOne_paired : PrefixPreserves (fun h _=>Paired h) Paired sendOne :=
  focus_paired HookJournal.SendEnvironment.one_appends HookJournal.send_environment_derived_frame
theorem consume_paired (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun h _=>Paired h) Paired (consume pid pkt ep) :=
  (focus_native_paired (ReceiveHookJournal.consume_appends pid pkt ep)
    (HookJournal.receive_consume_derived_frame pid pkt ep)).liftWGObserver.preserves

theorem stack_preserves (S : List Event → Prop) (packets : List (List UInt8)) :
    PrefixPreserves (fun h _=>S h) S (stack packets) :=
  PrefixEnsures.preserves (PrefixEnsures.lift _ (fun _ _ hi=>hi) (fun _ _ _ _ hi _=>hi))

theorem transmit_appends (pid : PeerId) : Appends (transmit pid) := Appends.focus _ _ _
theorem sendOne_appends : Appends sendOne := Appends.focus _ _ _
theorem consume_appends (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Appends (consume pid pkt ep) := (StateAppends.focus _ _ _).liftWGObserver
theorem stack_appends (packets : List (List UInt8)) : Appends (stack packets) :=
  Appends.lift _
end Leanux.Proofs.WG.TimerDiscipline.HookCommon
