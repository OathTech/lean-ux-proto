import Leanux.Proofs.WG.TimerDiscipline.HookTransmitClaims
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Queues.RxWaitAppends
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.TransmitWorker
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes

/-- The shared tx-step prelude, ending at the actual completion call cut.
This is a local callback variant of TxDisposition.stepSource. -/
def prepare (pid : PeerId) : WG.M (Option (List SkbId × KeypairId × Bool)) := do
  let (first,q) ← (← getPeer pid).txQueue.peek
  setPeer pid {(← getPeer pid) with txQueue := q}
  let go ← WG.andM (branch .txPacket first.isSome) do
    let some f := first | invariant "unreachable"
    let some h := f.head? | invariant "an empty ring item"
    branch .txNotUncrypted ((← getTxSkb h).state != .uncrypted)
  if !go then return none
  let some item := first | invariant "unreachable"
  let some headId := item.head? | invariant "an empty ring item"
  let head ← getTxSkb headId
  setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}
  let crypted ← branch .txCrypted (head.state == .crypted)
  return some (item,head.keypair,crypted)

def stepWith {m : Type → Type} [Monad m]
    (quiet : {α : Type} → WG.M α → m α)
    (complete : PeerId → List SkbId → m Unit) (pid : PeerId) : m Bool := do
  let selected ← quiet (prepare pid)
  match selected with
  | none => return false
  | some (item,key,crypted) =>
    if crypted then complete pid item
    quiet (TxDisposition.disposeSource pid item key)

theorem source (pid : PeerId) :
    stepWith (fun {_} a=>a) createDataDone pid = txStep pid := by
  rw [←TxDisposition.stepSource_eq]
  unfold stepWith prepare TxDisposition.stepSource TxDisposition.bodySource
  simp only [bind_assoc]
  repeat' first
    | rfl
    | (apply bind_congr; intro x)
    | (simp only [bind_assoc, pure_bind])
    | (first | exact rfl | simp only [Leanux.invariant])
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

def observed (pid : PeerId) : WGPrefix Receipt Bool :=
  stepWith (fun {_} a=>liftWGPrefix a) Transmit.observed pid

theorem erases (pid : PeerId) : ErasesStatePrefix (observed pid) (txStep pid) := by
  rw [←source]
  unfold observed stepWith
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  rintro (_ | ⟨item,key,crypted⟩)
  · exact erasesStatePrefix_pure _
  · cases crypted
    · exact erasesStatePrefix_lift _
    · exact erasesStatePrefix_bind (Transmit.erases pid item) (fun _=>erasesStatePrefix_lift _)

theorem preserves (pid : PeerId) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (observed pid) := by
  unfold observed stepWith
  apply (Transmit.quiet _).bind
  rintro (_ | ⟨item,key,crypted⟩)
  · exact StatePrefixEnsures.pure _ (fun _ _ _ hi=>hi) (fun _ _ _ hi=>hi)
  · cases crypted
    · exact Transmit.quiet _
    · exact (Transmit.preserves pid item).bind (fun _=>Transmit.quiet _)

theorem completion_appends (pid : PeerId) (items : List SkbId) :
    StateAppends (Transmit.observed pid items) := by
  unfold Transmit.observed Transmit.withHooks
  repeat' first
    | exact observed_appends _ _
    | exact StateAppends.lift _
    | exact StateAppends.pure _
    | apply StateAppends.bind
    | split
    | (intro x; try dsimp only)

theorem appends (pid : PeerId) : StateAppends (observed pid) := by
  unfold observed stepWith
  apply (StateAppends.lift _).bind
  rintro (_ | ⟨item,key,crypted⟩)
  · exact StateAppends.pure _
  · cases crypted
    · exact StateAppends.lift _
    · exact (completion_appends pid item).bind (fun _=>StateAppends.lift _)

def iteration (pid : PeerId) : PrefixM Receipt IterResult :=
  workerIterPrefix .txWorker (some pid) (liftWGObserver (observed pid))
    (do liftPrefix (branch .txNeedResched (←liftPrefix (Env.condResched .txWorker))))

theorem iteration_erases (pid : PeerId) :
    ErasesPrefix (iteration pid) (txIter pid (Env.condResched .txWorker)) :=
  workerIterPrefix_erases _ _ (liftWGObserver_erases (erases pid))
    (erasesPrefix_bind (erasesPrefix_lift _) (fun _=>erasesPrefix_lift _))

theorem iteration_preserves (pid : PeerId) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (iteration pid) := by
  have quiet {α : Type} (a : Leanux.M α) :
      PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (liftPrefix a) :=
    (PrefixEnsures.lift (P:=fun h _=>ValidHistory h) (S:=ValidHistory)
      (Q:=fun _ h _=>ValidHistory h) a (fun _ _ hi=>hi) (fun _ _ _ _ hi _=>hi)).preserves
  exact workerIterPrefix_preserves _ _ (fun _ _ hi=>hi)
    (preserves pid).liftWGObserver.preserves
    ((quiet _).bind (fun _=>quiet _))

theorem iteration_appends (pid : PeerId) : Appends (iteration pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.workerIter_appends)
    .txWorker (some pid) (appends pid).liftWGObserver
    ((Appends.lift _).bind (fun _=>Appends.lift _))

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.TransmitWorker
