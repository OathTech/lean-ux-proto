import Leanux.Proofs.WG.RetirementSecurity.KeySlotDataWorkers
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceScheduler
import Leanux.Proofs.WG.TransmitSecurity.DriverWorkersProjection

/-! Published-slot liveness through actual worker scheduling. The existing
SourceScheduler factor supplies all scheduling and stop cases; native source
callbacks retain the data projection independently from event chronology. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotScheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open KeySlotLiveness TransmitSecurity

theorem work_queue (f : List PeerId → List PeerId) :
    Preserves (InvExcept pending) (modifyDev fun d => {d with txWorkQueue:=f d.txWorkQueue}) := by
  exact modify _ (fun _=>rfl)

theorem crypt_ahead (pid : PeerId) :
    Preserves (fun w : World => InvExcept pending w.wg) (Env.cryptAhead pid) := by
  let P := fun w : World => InvExcept pending w.wg
  have readPeer (id : PeerId) : Preserves P (monadLift (getPeer id) : Leanux.M Peer) :=
    PublicationPoll.native_product (InvExcept pending) _ (getPeer_preserves _ _)
  have readPacket (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product (InvExcept pending)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    exact (Packets.getTxSkb_current id w v result a b run).1 ▸ before
  have queue (f : List PeerId → List PeerId) : Preserves P
      (monadLift (modifyDev fun d => {d with txWorkQueue:=f d.txWorkQueue}) : Leanux.M Unit) :=
    PublicationPoll.native_product (InvExcept pending) _ (work_queue f)
  have enqueue : Preserves P (monadLift (modifyDev fun d => {d with txWorkQueue:=d.txWorkQueue ++ [pid]}) : Leanux.M Unit) := queue (· ++ [pid])
  have dequeue : Preserves P (monadLift (modifyDev fun d => {d with txWorkQueue:=d.txWorkQueue.erase pid}) : Leanux.M Unit) := queue (·.erase pid)
  have encrypt : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    encrypt_iteration
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  have stop {α : Type} (e : Stop) : Preserves P (throw e : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v before run
    cases run
  routing_tx_source [Env.cryptAhead,getAmbient,modifyAmbient,peekHiddenSite] using [readPeer,readPacket,enqueue,dequeue,encrypt,ambient,stop]

theorem iteration (act : Activation) :
    Preserves (fun w : World => InvExcept pending w.wg) (Env.Activation.iter act) := by
  let P := fun w : World => InvExcept pending w.wg
  have crypt : ∀pid,Preserves P (Env.cryptAhead pid) := crypt_ahead
  have encrypt : Preserves P (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
    encrypt_iteration
  have decrypt : Preserves P (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
    decrypt_iteration
  have tx (pid : PeerId) : Preserves P (txIter pid (Env.condResched .txWorker)) := tx_iteration pid
  have receive : Preserves P (workerIter .receiveWorker none (monadLift receiveStep) (Env.condResched .receiveWorker)) :=
    handshake_iteration
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [Env.Activation.iter] using [crypt,encrypt,decrypt,tx,receive,ambient]

private theorem lift_native {E α : Type} {a : Leanux.M α}
    (keeps : Preserves (fun w : World => InvExcept pending w.wg) a) :
    PrefixPreserves (fun (_ : List E) w => InvExcept pending w.wg) (fun _ => True) (liftPrefix a) :=
  PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v before run => (hoare_iff_run _ _ _).mp keeps w x v before run)

theorem schedule (stack : Option Worker) :
    Preserves (fun w : World => InvExcept pending w.wg) (Env.schedule stack) := by
  have observed : PrefixPreserves (fun (_ : List Unit) w => InvExcept pending w.wg) (fun _ => True)
      (SourceScheduler.schedule (fun act => liftPrefix (Env.Activation.iter act))
        (liftPrefix Env.napiSoftirq) stack) := by
    apply SourceScheduler.schedule_preserves (fun _ _ _ => True.intro)
    · intro h w v same before
      exact store_transport (congrArg (fun s : ProductStore43 => s.2.2.2) same) before
    · intro pid
      exact lift_native (PublicationPoll.native_product (InvExcept pending) _ (work_queue (·.erase pid)))
    · intro act
      exact lift_native (iteration act)
    · exact lift_native (KeySlotNapi.softirq pending)
  have erases := SourceScheduler.schedule_erases (Event:=Unit)
    (fun act => liftPrefix (Env.Activation.iter act)) (liftPrefix Env.napiSoftirq)
    (fun _ => erasesPrefix_lift _) (erasesPrefix_lift _) stack
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have actual := (erases w []).trans run
  have post := (observed w [] before).choose_spec.2.2
  rw [actual] at post
  exact post

theorem shared {E : Type} {ρ : E → Option Nonce.Allocation} {hooks : Driver.Hooks E}
    (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : InvExcept pending w.wg) (stack : Option Worker) (h : List E)
    (run : (runPrefix (Driver.scheduleObserved hooks stack) w h).1 = .ok ((),v)) :
    InvExcept pending v.wg := by
  have projected := Driver.schedule_projects projects stack
  rw [Driver.nonce_scheduleObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (schedule stack) w () v before
    (DriverOwnership.product_native projected (Nonce.scheduleObserved_erases stack) w v h run)

end Leanux.Proofs.WG.RetirementSecurity.KeySlotScheduler
