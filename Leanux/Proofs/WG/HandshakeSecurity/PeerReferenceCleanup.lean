import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEnvironment

/-! Namespace cleanup retains resident positivity and has no exchange callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem env_cleanup : Framing.Preserves (fun w : World => Inv w.wg) Env.netnsCleanup := by
  have preExit : Framing.Preserves (fun w : World => Inv w.wg)
      (monadLift netnsPreExit : Leanux.M Unit) := PublicationPoll.native_product Inv netnsPreExit pre_exit
  have effect {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => Inv w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have route {α : Type} (a : Net.M α) :
      Framing.Preserves (fun w : World => Inv w.wg) (monadLift a : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w value v before run
    have frame : SameProductStore (monadLift a : Leanux.M α) :=
      fun s => productRouting_spec a (fun t => t = s)
    have same := (ProjectedAction.iff_run _ _ _).mp frame w value v run
    have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
    apply of_residents
    intro d pid peer found stored
    exact resident before (device.symm.trans found) stored
  have env (f : EnvWorld → EnvWorld) :
      Framing.Preserves (fun w : World => Inv w.wg) (modifyEnv f) := by
    unfold modifyEnv
    apply hoare_modify
    exact fun _ hi => hi
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [preExit,effect,route,env]

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
