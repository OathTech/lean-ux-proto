import Leanux.Proofs.WG.TimerDiscipline.HookInitializedSource
/-! Whole initialized outcomes and concrete configuration/syscall journals.
Global allocation uniqueness is a separate state-dependent frontier claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged HandshakeJournal Lifetimes

theorem original_peerCommand (attrs : PeerAttrs) :
    (do let result←inspect (liftWGObserver (peerCommand attrs));pure result.1)=
      Campaign2.Product.inspect (liftWG (setPeerCmd attrs)) ∧
    Campaign2.Product.Returns (inspect (liftWGObserver (peerCommand attrs))) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (liftWGObserver_erases (peerCommand_erases attrs)),
    inspect_facts _ (peerCommand_valid attrs).liftWGObserver.preserves
      (peerCommand_paired attrs).liftWGObserver.preserves⟩

theorem original_deviceCommand (attrs : DeviceAttrs) :
    (do let result←inspect (liftWGObserver (deviceCommand attrs));pure result.1)=
      Campaign2.Product.inspect (liftWG (wgSetDevice attrs)) ∧
    Campaign2.Product.Returns (inspect (liftWGObserver (deviceCommand attrs))) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (liftWGObserver_erases (deviceCommand_erases attrs)),
    inspect_facts _ (deviceCommand_valid attrs).liftWGObserver.preserves
      (deviceCommand_paired attrs).liftWGObserver.preserves⟩

theorem original_syscall (c : Syscall) :
    (do let result←inspect (syscall c);pure result.1)=Campaign2.Product.inspect (Leanux.syscall c) ∧
    Campaign2.Product.Returns (inspect (syscall c)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (syscall_erases c),inspect_facts _ (syscall_valid c) (syscall_paired c)⟩

theorem original_initialized (trace : Trace) (placeholders : Bool) :
    (Initialized.inspection trace placeholders).1.map Prod.fst=Runner.executeTrace trace placeholders ∧
    Facts (Initialized.inspection trace placeholders).2 :=
  ⟨Initialized.inspection_json trace placeholders,Initialized.inspection_facts trace placeholders⟩

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
