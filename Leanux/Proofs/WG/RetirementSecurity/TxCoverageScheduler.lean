import Leanux.Proofs.WG.RetirementSecurity.TxCoverageTx
import Leanux.Proofs.WG.TransmitSecurity.DriverWorkersProjection

/-! TX resident-cell coverage through the actual native scheduler. The existing
campaign-1 SourceScheduler factor supplies control-flow composition; its
callbacks below are original native actions, with no new outer runner or
inferred event chronology. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageScheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TransmitSecurity RetirementSecurity TxCoverageNative TxCoverageStack

theorem work_queue (f : List PeerId → List PeerId) :
    Preserves (TxCoverage locals) (modifyDev fun d => {d with txWorkQueue:=f d.txWorkQueue}) := by
  exact TxCoverageNative.modify_device _ (fun _ => rfl) (fun _ => rfl)

theorem crypt_ahead (pid : PeerId) :
    Preserves (fun w : World => TxCoverage locals w.wg) (Env.cryptAhead pid) := by
  let P := fun w : World => TxCoverage locals w.wg
  have readPeer (id : PeerId) : Preserves P (monadLift (getPeer id) : Leanux.M Peer) :=
    PublicationPoll.native_product (TxCoverage locals) _ (getPeer_preserves _ _)
  have readPacket (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product (TxCoverage locals)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    exact (Packets.getTxSkb_current id w v result a b run).1 ▸ before
  have queue (f : List PeerId → List PeerId) : Preserves P
      (monadLift (modifyDev fun d => {d with txWorkQueue:=f d.txWorkQueue}) : Leanux.M Unit) :=
    PublicationPoll.native_product (TxCoverage locals) _ (work_queue f)
  have enqueue : Preserves P (monadLift (modifyDev fun d => {d with txWorkQueue:=d.txWorkQueue ++ [pid]}) : Leanux.M Unit) := queue (· ++ [pid])
  have dequeue : Preserves P (monadLift (modifyDev fun d => {d with txWorkQueue:=d.txWorkQueue.erase pid}) : Leanux.M Unit) := queue (·.erase pid)
  have encrypt : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    TxCoverageEncrypt.iteration
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  have stop {α : Type} (e : Stop) : Preserves P (throw e : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v before run
    cases run
  routing_tx_source [Env.cryptAhead,getAmbient,modifyAmbient,peekHiddenSite] using [readPeer,readPacket,enqueue,dequeue,encrypt,ambient,stop]

theorem iteration (act : Activation) :
    Preserves (fun w : World => TxCoverage locals w.wg) (Env.Activation.iter act) := by
  let P := fun w : World => TxCoverage locals w.wg
  have crypt : ∀pid,Preserves P (Env.cryptAhead pid) := crypt_ahead
  have encrypt : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    TxCoverageEncrypt.iteration
  have decrypt : Preserves P (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
    TxCoverageDecrypt.iteration
  have tx (pid : PeerId) : Preserves P (txIter pid (Env.condResched .txWorker)) := TxCoverageWorkers.transmit pid
  have receive : Preserves P (workerIter .receiveWorker none (monadLift receiveStep) (Env.condResched .receiveWorker)) :=
    TxCoverageWorkers.receive
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [Env.Activation.iter] using [crypt,encrypt,decrypt,tx,receive,ambient]

private theorem lift_native {E α : Type} {a : Leanux.M α}
    (keeps : Preserves (fun w : World => TxCoverage locals w.wg) a) :
    PrefixPreserves (fun (_ : List E) w => TxCoverage locals w.wg) (fun _ => True) (liftPrefix a) :=
  PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v before run => (hoare_iff_run _ _ _).mp keeps w x v before run)

theorem schedule (stack : Option Worker) :
    Preserves (fun w : World => TxCoverage locals w.wg) (Env.schedule stack) := by
  have observed : PrefixPreserves (fun (_ : List Unit) w => TxCoverage locals w.wg) (fun _ => True)
      (SourceScheduler.schedule (fun act => liftPrefix (Env.Activation.iter act))
        (liftPrefix Env.napiSoftirq) stack) := by
    apply SourceScheduler.schedule_preserves (fun _ _ _ => True.intro)
    · intro h w v same before
      exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) before
    · intro pid
      exact lift_native (PublicationPoll.native_product (TxCoverage locals) _ (work_queue (·.erase pid)))
    · intro act
      exact lift_native (iteration act)
    · exact lift_native (TxCoverageNapi.softirq locals)
  have erases := SourceScheduler.schedule_erases (Event:=Unit)
    (fun act => liftPrefix (Env.Activation.iter act)) (liftPrefix Env.napiSoftirq)
    (fun _ => erasesPrefix_lift _) (erasesPrefix_lift _) stack
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have actual := (erases w []).trans run
  have post := (observed w [] before).choose_spec.2.2
  rw [actual] at post
  exact post

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageScheduler
