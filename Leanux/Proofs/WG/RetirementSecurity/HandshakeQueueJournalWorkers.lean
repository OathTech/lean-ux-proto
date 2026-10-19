import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalCallbacks
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! The shared driver retains validated handshake inputs through crypt/TX
workers. Receive uses its actual checked-pop contract, including Stop prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option Nonce.Allocation}

theorem condResched_frame (worker : Worker) :
    SameView HandshakeLengths.productView (Env.condResched worker) :=
  (condResched_sameKernel worker).of_factor
    (fun store : ProductStore43=>store.2.2.2.dev.map fun d=>d.handshakeQueue)
    HandshakeLengths.productView (fun _=>rfl)

theorem encryption_iteration (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.encryptIterObserved hooks) := by
  have history : Driver.ProductHistorySafe Safe (Driver.encryptIterObserved hooks) :=
    (show Driver.encryptIterObserved (quietHooks hooks)=Driver.encryptIterObserved hooks from rfl) ▸
      Driver.encryptIter_history c.quiet
  have projected:=Driver.encryptIter_projects c.projects
  rw [Driver.nonce_encryptIterObserved_eq] at projected
  exact product_native history projected Nonce.encryptIterObserved_erases (product_frame actualEncryptIter_cell)

theorem tx_iteration (c : Contracts Valid Safe hooks ρ) (pid : PeerId) :
    ProductSafe Valid Safe (Driver.txIterObserved hooks pid) := by
  have history : Driver.ProductHistorySafe Safe (Driver.txIterObserved hooks pid) :=
    (show Driver.txIterObserved (quietHooks hooks) pid=Driver.txIterObserved hooks pid from rfl) ▸
      Driver.txIter_history c.quiet pid
  have projected:=Driver.txIter_projects c.projects pid
  rw [Driver.nonce_txIterObserved_eq] at projected
  exact product_native history projected (Nonce.txIterObserved_erases pid)
    (product_frame (txIter_cell pid _ (condResched_frame .txWorker)))

theorem decrypt_iteration (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.decryptIterObserved hooks) := by
  have history : Driver.ProductHistorySafe Safe (Driver.decryptIterObserved hooks) :=
    (show Driver.decryptIterObserved (quietHooks hooks)=Driver.decryptIterObserved hooks from rfl) ▸
      Driver.decryptIter_history c.quiet
  have projected:=Driver.decryptIter_projects c.projects
  rw [Driver.nonce_decryptIterObserved_eq] at projected
  exact product_native history projected Nonce.decryptIterObserved_erases
    (product_frame (decryptIter_cell _ _ _ napiSoftirq_cell napiIrqExit_cell (condResched_frame .decryptWorker)))

theorem receive_iteration (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves .receiveWorker none (fun _ _ before=>before.2)
    (state_product c.handshake)
    (product_lift Valid Safe _ (product_frame (condResched_frame .receiveWorker)))

theorem product_wg (action : WG.M α) (same : SameView view action) :
    ProductSafe Valid Safe (liftPrefix (liftWG action)) := by
  simpa only [liftWGObserver_lift] using state_product (state_frame Valid Safe same)

theorem product_stop (stop : Stop) : ProductSafe Valid Safe (liftPrefix (throw stop : Leanux.M α)) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w value v before run
  cases run

theorem crypt_ahead (c : Contracts Valid Safe hooks ρ) (pid : PeerId) :
    ProductSafe Valid Safe (Driver.cryptAheadObserved hooks pid) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encryption_iteration c)
    | (scheduler_preserve_at getPeer; exact product_wg _ (getPeer_frame _))
    | (scheduler_preserve_at getTxSkb; exact product_wg _ (by handshake_cell_source [] using []))
    | (scheduler_preserve_at modifyDev; exact product_wg _ (modifyDev_cell _ (fun _=>rfl)))
    | (scheduler_preserve_at throw; exact product_stop _)
    | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
             | scheduler_preserve_at peekHiddenSite | scheduler_preserve_at invariant
       exact product_ambient Valid Safe _)
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure Valid Safe _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | driver_history_join_let
    | driver_history_join_use
    | maintenance_intro
    | driver_history_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration (c : Contracts Valid Safe hooks ρ) (a : Activation) :
    ProductSafe Valid Safe (Driver.iterationObserved hooks a) := by
  change PrefixPreserves (ProductInv Valid Safe) Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encryption_iteration c)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration c)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration c)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration c _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead c _)
    | (scheduler_preserve_at invariant; exact product_ambient Valid Safe _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | driver_history_join_let
    | driver_history_join_use
    | maintenance_intro
    | driver_history_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (c : Contracts Valid Safe hooks ρ) (stack : Option Worker) :
    ProductSafe Valid Safe (Driver.scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (fun _ _ before=>before.2)
  · intro h w v same before
    refine ⟨transport ?_ before.1,before.2⟩
    exact congrArg (fun store : ProductStore43=>store.2.2.2.dev.map fun d=>d.handshakeQueue) same
  · intro pid
    exact product_wg _ (modifyDev_cell _ (fun _=>rfl))
  · exact iteration c
  · exact softirq c

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
