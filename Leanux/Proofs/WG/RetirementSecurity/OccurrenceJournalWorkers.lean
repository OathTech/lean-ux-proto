import Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncryptionJournal
import Leanux.Proofs.WG.Queues.SchedulerPreservation

/-! Other native worker iterations preserve the physical poll certificates.
Their source terms contain no encryption poll; crypt-ahead is composed with
the checked actual encryption iteration separately. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open OccurrenceStack TransmitSecurity

abbrev ProductSafe (g : PrefixM Journal.Event α) := PrefixPreserves (Inv []) Safe g

theorem checked_history {E α : Type} {P : World → Prop} {S : List E → Prop}
    {g : PrefixM E α} (history : Driver.ProductHistorySafe S g)
    (native : ∀ w h result v, P w → (runPrefix g w h).1 = .ok (result,v) → P v) :
    PrefixPreserves (fun h w => P w ∧ S h) S g := by
  intro w h before
  obtain ⟨suffix,extension,safe,normal⟩ := history w h before.2
  refine ⟨suffix,extension,safe,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok output => exact ⟨native w h output.1 output.2 before.1 result,safe⟩

theorem join_history {g : PrefixM Journal.Event α}
    (history : Driver.ProductHistorySafe Safe g)
    (native : ∀ w h result v, Ready [] [] w.wg →
      (runPrefix g w h).1 = .ok (result,v) → Ready [] [] v.wg) : ProductSafe g :=
  checked_history history native

theorem product_lift (action : Leanux.M α)
    (native : Preserves (fun w : World => Ready [] [] w.wg) action) : ProductSafe (liftPrefix action) :=
  join_history (Driver.History.product_lift _) (fun w h result v before run =>
    (hoare_iff_run _ _ _).mp native w result v before (by simpa only [runPrefix_lift] using run))

theorem product_native (action : WG.M α) (native : Preserves (Ready [] []) action) :
    ProductSafe (liftPrefix (liftWG action)) :=
  product_lift _ (PublicationPoll.native_product _ _ native)

theorem product_ambient (action : AmbientM α) :
    ProductSafe (liftPrefix (monadLift action : Leanux.M α)) :=
  product_lift _ (productAmbient_spec action _ (fun _ _ hi => hi))

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2) value

theorem tx_iteration (pid : PeerId) : ProductSafe (Driver.txIterObserved Journal.hooks pid) := by
  apply join_history
  · exact (show Driver.txIterObserved nonpollHooks pid = Driver.txIterObserved Journal.hooks pid from rfl) ▸
      Driver.txIter_history hooks_safe.actors pid
  · intro w h result v before run
    have projected := Driver.txIter_projects Journal.hooks_projects pid
    rw [Driver.nonce_txIterObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp (OccurrenceTx.iteration pid) w result v before
      (DriverOwnership.product_native projected (Nonce.txIterObserved_erases pid) w v h run)

theorem decrypt_iteration : ProductSafe (Driver.decryptIterObserved Journal.hooks) := by
  apply join_history
  · exact (show Driver.decryptIterObserved nonpollHooks = Driver.decryptIterObserved Journal.hooks from rfl) ▸
      Driver.decryptIter_history hooks_safe.actors
  · intro w h result v before run
    have projected := Driver.decryptIter_projects Journal.hooks_projects
    rw [Driver.nonce_decryptIterObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp OccurrenceDecrypt.iteration w result v before
      (DriverOwnership.product_native projected Nonce.decryptIterObserved_erases w v h run)

theorem receive_iteration : ProductSafe (Driver.receiveIterObserved Journal.hooks) := by
  apply join_history
  · exact (show Driver.receiveIterObserved nonpollHooks = Driver.receiveIterObserved Journal.hooks from rfl) ▸
      Driver.receiveIter_history hooks_safe.actors
  · intro w h result v before run
    have projected := Driver.receiveIter_projects Journal.hooks_projects
    rw [Driver.nonce_receiveIterObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp OccurrenceHandshake.iteration w result v before
      (DriverOwnership.product_native projected Nonce.receiveIterObserved_erases w v h run)

theorem product_stop (e : Stop) : ProductSafe (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run

theorem product_work (f : List PeerId → List PeerId) : ProductSafe
    (liftPrefix (liftWG (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}))) :=
  product_native _ (OccurrenceScheduler.work_queue f)

theorem product_tx_read (id : SkbId) : ProductSafe (liftPrefix (liftWG (getTxSkb id))) := by
  apply product_native
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a packet v b before run
  exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ before

theorem crypt_ahead (pid : PeerId) : ProductSafe (Driver.cryptAheadObserved Journal.hooks pid) := by
  change PrefixPreserves (Inv []) Safe _
  unfold Driver.cryptAheadObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encryption_iteration)
    | (scheduler_preserve_at getPeer; exact product_native _ (getPeer_preserves _ _))
    | (scheduler_preserve_at getTxSkb; exact product_tx_read _)
    | (scheduler_preserve_at modifyDev; first
       | exact product_work (fun q => q ++ [pid])
       | exact product_work (fun q => q.erase pid))
    | (scheduler_preserve_at throw; exact product_stop _)
    | (first | scheduler_preserve_at getAmbient | scheduler_preserve_at modifyAmbient
             | scheduler_preserve_at peekHiddenSite | scheduler_preserve_at invariant
       exact product_ambient _)
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | driver_history_join_let
    | driver_history_join_use
    | maintenance_intro
    | driver_history_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem iteration (a : Activation) : ProductSafe (Driver.iterationObserved Journal.hooks a) := by
  change PrefixPreserves (Inv []) Safe _
  unfold Driver.iterationObserved
  repeat' first
    | (nonce_product_head Driver.encryptIterObserved; exact encryption_iteration)
    | (nonce_product_head Driver.decryptIterObserved; exact decrypt_iteration)
    | (nonce_product_head Driver.receiveIterObserved; exact receive_iteration)
    | (nonce_product_head Driver.txIterObserved; exact tx_iteration _)
    | (nonce_product_head Driver.cryptAheadObserved; exact crypt_ahead _)
    | (scheduler_preserve_at invariant; exact product_ambient _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ite; apply PrefixPreserves.ite)
    | driver_history_join_let
    | driver_history_join_use
    | maintenance_intro
    | driver_history_reduce
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved Journal.hooks stack) := by
  apply SourceScheduler.schedule_preserves (fun _ _ hi => hi.2)
  · intro h w v same before
    exact ⟨ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) before.1,before.2⟩
  · intro pid
    exact product_work (fun q => q.erase pid)
  · exact iteration
  · exact softirq

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
