import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerReceiveSource
import Leanux.Proofs.WG.TimerDiscipline.HookStateFrames
import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Queues.RxWaitAppends

/-! Generic hook-aware worker assembly. Event and history predicate remain
parameters. Actual transmit, receive, and NAPI callbacks must be provided;
only non-hook preparation, encryption, payment and scheduling atoms are quiet. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open RxHistory.SchedulerSource
variable {E : Type}

structure HistoryContracts (S : List E → Prop) (c : Callbacks E) : Prop where
  transmit : ∀ pid, PrefixPreserves (fun h _=>S h) S (c.transmit pid)
  receive : PrefixPreserves (fun h _=>S h) S c.receive
  softirq : PrefixPreserves (fun h _=>S h) S c.softirq
  irq : PrefixPreserves (fun h _=>S h) S c.irq

structure AppendContracts (c : Callbacks E) : Prop where
  transmit : ∀ pid, Appends (c.transmit pid)
  receive : Appends c.receive
  softirq : Appends c.softirq
  irq : Appends c.irq

def old {α : Type} (a : RxHistory.Obs α) : PrefixM E α :=
  liftPrefix (fun w=>(runPrefix a w []).1)

theorem old_eq {α : Type} (a : RxHistory.Obs α) (native : Leanux.M α)
    (erases : ErasesPrefix a native) : old (E:=E) a = liftPrefix native := by
  apply congrArg liftPrefix
  funext w
  exact erases w []

theorem quiet (S : List E → Prop) {α : Type} (a : Leanux.M α) :
    PrefixPreserves (fun h _=>S h) S (liftPrefix a) :=
  PrefixEnsures.preserves (PrefixEnsures.lift a (fun _ _ hi=>hi) (fun _ _ _ _ hi _=>hi))

theorem atoms (S : List E → Prop) :
    AtomContracts (fun h _=>S h) S (fun {_} a=>old a) := by
  constructor
  all_goals intros; exact quiet S _

def encrypt (c : Callbacks E) : PrefixM E IterResult := do
  let item ← liftPrefix (liftWG TxRing.pollSource)
  c.softirq
  liftPrefix (RxWorkers.encryptTailSource item)

def decryptStep (c : Callbacks E) : PrefixM E Bool :=
  RxWorkers.decryptWith (liftPrefix (liftWG RxWorkers.prepareSource))
    (fun pid=>liftPrefix (liftWG (peerPut (some pid)))) c.softirq c.irq

def decrypt (c : Callbacks E) : PrefixM E IterResult :=
  workerIterPrefix .decryptWorker none (decryptStep c)
    (do liftPrefix (branch .decWorkerNeedResched (←liftPrefix (Env.condResched .decryptWorker))))

theorem encrypt_erases (c : Callbacks E) (h : ErasureContracts c) :
    ErasesPrefix (encrypt c)
      (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun item =>
    erasesPrefix_bind h.softirq (fun _=>erasesPrefix_lift _))

theorem decryptStep_erases (c : Callbacks E) (h : ErasureContracts c) :
    ErasesPrefix (decryptStep c) (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  NapiSource.decrypt_erases (erasesPrefix_lift _) (fun _=>erasesPrefix_lift _) h.softirq h.irq

theorem decrypt_erases (c : Callbacks E) (h : ErasureContracts c) :
    ErasesPrefix (decrypt c)
      (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  workerIterPrefix_erases _ _ (decryptStep_erases c h)
    (erasesPrefix_bind (erasesPrefix_lift _) (fun _=>erasesPrefix_lift _))

structure StateContracts (I : List E → World → Prop) (S : List E → Prop)
    (c : Callbacks E) : Prop where
  transmit : ∀ pid, PrefixPreserves I S (c.transmit pid)
  receive : PrefixPreserves I S c.receive
  softirq : PrefixPreserves I S c.softirq
  irq : PrefixPreserves I S c.irq

structure StateLeaves (I : List E → World → Prop) (S : List E → Prop) : Prop where
  atoms : AtomContracts I S (fun {_} a => old a)
  poll : PrefixPreserves I S (liftPrefix (liftWG TxRing.pollSource))
  tail : ∀ item, PrefixPreserves I S (liftPrefix (RxWorkers.encryptTailSource item))
  prepare : PrefixPreserves I S (liftPrefix (liftWG RxWorkers.prepareSource))
  put : ∀ pid, PrefixPreserves I S (liftPrefix (liftWG (peerPut (some pid))))

theorem history_state (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    StateContracts (fun h _ => S h) S c :=
  ⟨h.transmit,h.receive,h.softirq,h.irq⟩

theorem history_leaves (S : List E → Prop) : StateLeaves (fun h _ => S h) S :=
  ⟨atoms S,quiet S _,fun _ => quiet S _,quiet S _,fun _ => quiet S _⟩

theorem encrypt_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) :
    PrefixPreserves I S (encrypt c) :=
  leaves.poll.bind (fun _ => h.softirq.bind (fun _ => leaves.tail _))

theorem decryptStep_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) :
    PrefixPreserves I S (decryptStep c) :=
  NapiSource.decrypt_preserves safe leaves.prepare leaves.put h.softirq h.irq

theorem decrypt_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) :
    PrefixPreserves I S (decrypt c) :=
  workerIterPrefix_preserves _ _ safe (decryptStep_preserves_state safe c h leaves)
    ((HookState.lift_store safe store _ (condResched_sameKernel _)).bind
      (fun _ => HookState.ambient safe store (AmbientM.branch _ _)))

theorem receive_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) :
    PrefixPreserves I S (receive c) :=
  workerIterPrefix_preserves _ _ safe h.receive
    (HookState.lift_store safe store _ (condResched_sameKernel _))

theorem encrypt_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    PrefixPreserves (fun h _=>S h) S (encrypt c) :=
  encrypt_preserves_state c (history_state S c h) (history_leaves S)

theorem decryptStep_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    PrefixPreserves (fun h _=>S h) S (decryptStep c) :=
  decryptStep_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi) c (history_state S c h) (history_leaves S)

theorem decrypt_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    PrefixPreserves (fun h _=>S h) S (decrypt c) :=
  decrypt_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) c
    (history_state S c h) (history_leaves S)

theorem receive_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) :
    PrefixPreserves (fun h _=>S h) S (receive c) :=
  receive_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) c (history_state S c h)

theorem encrypt_appends (c : Callbacks E) (h : AppendContracts c) : Appends (encrypt c) :=
  (Appends.lift _).bind (fun _=>h.softirq.bind (fun _=>Appends.lift _))

theorem decryptStep_appends (c : Callbacks E) (h : AppendContracts c) : Appends (decryptStep c) :=
  NapiSource.decrypt_appends (Appends.lift _) (fun _=>Appends.lift _) h.softirq h.irq

theorem decrypt_appends (c : Callbacks E) (h : AppendContracts c) : Appends (decrypt c) :=
  NapiSource.workerIter_appends _ _ (decryptStep_appends c h)
    ((Appends.lift _).bind (fun _=>Appends.lift _))

theorem receive_appends (c : Callbacks E) (h : AppendContracts c) : Appends (receive c) :=
  NapiSource.workerIter_appends _ _ h.receive (Appends.lift _)

def ahead (c : Callbacks E) (pid : PeerId) : PrefixM E Unit :=
  cryptAheadWith (fun {_} a=>old a) (encrypt c) pid

def iteration (c : Callbacks E) (a : Activation) : PrefixM E IterResult :=
  iterationWith (fun {_} a=>old a) (encrypt c) (ahead c) c.transmit (decrypt c) (receive c) a

theorem ahead_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (pid : PeerId) :
    PrefixPreserves I S (ahead c pid) :=
  cryptAhead_preserves safe _ leaves.atoms _ (encrypt_preserves_state c h leaves) pid

theorem iteration_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (a : Activation) :
    PrefixPreserves I S (iteration c a) :=
  RxHistory.SchedulerSource.iteration_preserves _ leaves.atoms _ _ _ _ _
    (encrypt_preserves_state c h leaves) (ahead_preserves_state safe c h leaves) h.transmit
    (decrypt_preserves_state safe store c h leaves) (receive_preserves_state safe store c h) a

theorem ahead_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (pid : PeerId) : PrefixPreserves (fun h _=>S h) S (ahead c pid) :=
  ahead_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi) c (history_state S c h) (history_leaves S) pid

theorem iteration_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (a : Activation) : PrefixPreserves (fun h _=>S h) S (iteration c a) :=
  iteration_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) c
    (history_state S c h) (history_leaves S) a

theorem ahead_appends (c : Callbacks E) (h : AppendContracts c) (pid : PeerId) :
    Appends (ahead c pid) :=
  cryptAhead_appends _ (fun _ _=>Appends.lift _) _ (encrypt_appends c h) pid

theorem iteration_appends (c : Callbacks E) (h : AppendContracts c) (a : Activation) :
    Appends (iteration c a) :=
  RxHistory.SchedulerSource.iteration_appends _ (fun _ _=>Appends.lift _) _ _ _ _ _
    (encrypt_appends c h) (ahead_appends c h) h.transmit
    (decrypt_appends c h) (receive_appends c h) a

/-- Erase only the unchanged RX access atoms. No committed hook-bearing
worker is passed to this embedding. -/
theorem old_lift {α : Type} (a : Leanux.M α) :
    old (E:=E) (RxHistory.mixed (liftPrefix a)) = liftPrefix a :=
  old_eq _ _ (RxHistory.mixed_erases (erasesPrefix_lift a))

theorem old_native {α : Type} (a : WG.M α) :
    old (E:=E) (RxHistory.mixed (liftWGObserver (liftWGPrefix a))) = liftPrefix (liftWG a) :=
  old_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift a)))

theorem old_peer (pid : PeerId) :
    old (E:=E) (RxHistory.mixed (liftWGObserver (getPeerMixed pid))) = liftPrefix (liftWG (getPeer pid)) :=
  old_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (getPeerMixed_erases pid)))

theorem old_packet (id : SkbId) :
    old (E:=E) (RxHistory.mixed (liftWGObserver (getTxSkbPrefix id))) = liftPrefix (liftWG (getTxSkb id)) :=
  old_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (getTxSkbPrefix_erases id)))

theorem old_throw {α : Type} (stop : Stop) :
    old (E:=E) (RxHistory.mixed (throw stop : PrefixM LifetimeEvent α)) = liftPrefix (throw stop) :=
  old_eq _ _ (RxHistory.mixed_erases (erasesPrefix_throw stop))

theorem ahead_erases (c : Callbacks E) (h : ErasureContracts c) (pid : PeerId) :
    ErasesPrefix (ahead c pid) (Env.cryptAhead pid) := by
  unfold ahead cryptAheadWith Env.cryptAhead
  simp only [old_lift,old_native,old_peer,old_packet,old_throw]
  repeat' first
    | exact encrypt_erases c h
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro

theorem iteration_erases (c : Callbacks E) (h : ErasureContracts c) (a : Activation) :
    ErasesPrefix (iteration c a) (Env.Activation.iter a) := by
  unfold iteration iterationWith Env.Activation.iter
  simp only [old_lift]
  repeat' first
    | exact encrypt_erases c h
    | exact decrypt_erases c h
    | exact ahead_erases c h _
    | exact h.transmit _
    | exact receive_erases c h
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | maintenance_intro


end Leanux.Proofs.WG.TimerDiscipline.HookScheduler
