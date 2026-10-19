import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteHandshakeObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeWorker

/-! Complete native handshake-worker composition keeps forward entry facts
and converse terminal accounting on the same ledger at each source bind.
The supplied session and keepalive callbacks retain this same paired carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteHandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal CompletePassive
open CompleteCarrier (Accounted)
open HandshakeSecurity Origins.HandshakeSources
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem choice {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
    {Safe : List Event → Prop} (p : Prop) [Decidable p]
    {yes no : WGPrefix Event α}
    (hy : p → Checked debts locals Safe yes) (hn : ¬p → Checked debts locals Safe no) :
    Checked debts locals Safe (if p then yes else no) := by
  by_cases hp : p
  · simpa only [hp,ite_true] using hy hp
  · simpa only [hp,ite_false] using hn hp

open Lean Meta Elab Tactic in
elab "complete_checked_expand" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``CompletePassive.Checked do throwError "not a paired entry contract"
  evalTactic (← `(tactic| unfold CompletePassive.Checked StatePrefixPreserves))

macro "complete_handshake_step " safe:term " using " entry:term : tactic => `(tactic| first
  | complete_checked_expand
  | (maintenance_head CausalScope.scope; apply CompletePassive.scope $safe $entry)
  | (maintenance_head receiptWGObserved; refine CompletePassive.receipt $safe $entry _ _ ?_ (fun _ => rfl) (fun _ _ => rfl))
  | (maintenance_head HandshakeWorker.callback; apply CompletePassive.callback $safe $entry)
  | (maintenance_head HandshakeWorker.old; apply CompleteHandshake.old_call $safe $entry; solve | entry_handshake_frame)
  | (maintenance_head ProtocolSocket.observed; exact CompleteHandshake.protocol $safe $entry _ _)
  | (maintenance_head CookieSocket.observed; exact CompleteHandshake.cookie $safe $entry _ _ _)
  | (maintenance_head NestedPeerRelease.admitInitiationWith; exact CompleteHandshake.initiation $safe $entry _)
  | (maintenance_head NestedPeerRelease.admitResponseWith; exact CompleteHandshake.response $safe $entry _)
  | (maintenance_head NestedPeerRelease.cookieObserved; exact CompleteHandshake.cookie_consumed $safe $entry _)
  | (maintenance_head TimerEffects.derivedWith; exact CompleteTimer.derived $safe $entry _)
  | (maintenance_head TimerEffects.traversalWith; exact CompleteTimer.traversal $safe $entry _)
  | (maintenance_head StagedDisposal.Decoration.release; exact CompleteSource.original _ $safe $entry)
  | (maintenance_head captureWGRun;
     apply StatePrefixPreserves.captureWGObserved
     exact CompletePassive.native $safe $entry _ (by entry_handshake_frame))
  | (maintenance_head liftWGPrefix; exact CompletePassive.native $safe $entry _ (by entry_handshake_frame))
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head ite; apply choice)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => CompleteCarrier.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
variable (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
variable (sessions : ∀ pid, Checked debts locals Safe (session pid))
variable (keepalives : ∀ pid, Checked debts locals Safe (keepalive pid))

def make (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (mac : HandshakeMac) : Ops (WGPrefix Event) :=
  HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
    (ExchangeJoint.receiveOps Event.exchange
      (HandshakeEffects.withEffects (receiveOps session keepalive mac)
        (Event.old ∘ Journal.Event.handshake) effects))

include accountSafe sessions keepalives

omit keepalives in
theorem response_source (mac : HandshakeMac) (pid : PeerId) :
    Checked debts locals Safe (responseWith (make session keepalive mac) pid) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold responseWith make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (entry_callback_head session; exact sessions _)
    | complete_handshake_step Safe using accountSafe

theorem after_mac (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Checked debts locals Safe (afterMacWith (make session keepalive mac) msg src loaded state) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold afterMacWith make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (maintenance_head responseWith; exact response_source Safe accountSafe session keepalive sessions _ _)
    | (entry_callback_head session; exact sessions _)
    | (entry_callback_head keepalive; exact keepalives _)
    | complete_handshake_step Safe using accountSafe

theorem receive (msg : Key) (src : SkbSource) : Checked debts locals Safe
    (CookieConsumption.receiveWith
      (NestedPeerRelease.cookieObserved ConsumerSource.nested Event.cookieConsumed)
      (make session keepalive) msg src) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold CookieConsumption.receiveWith
  repeat' first
    | (maintenance_head afterMacWith; exact after_mac Safe accountSafe session keepalive sessions keepalives _ _ _ _ _)
    | complete_handshake_step Safe using accountSafe

theorem worker : Checked debts locals Safe (CausalJournal.handshake session keepalive) := by
  change StatePrefixEnsures (CompleteCarrier.Carrier debts locals) Safe _ (fun _ => CompleteCarrier.Carrier debts locals)
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (maintenance_head CookieConsumption.receiveWith; exact receive Safe accountSafe session keepalive sessions keepalives _ _)
    | complete_handshake_step Safe using accountSafe

omit sessions in
theorem session_worker : Checked debts locals Safe (CausalJournal.handshake CausalJournal.session keepalive) :=
  worker Safe accountSafe CausalJournal.session keepalive (CompleteHandshake.session Safe accountSafe) keepalives

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteHandshakeWorker
