import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeObserved

/-! Full entry accounting through the actual enriched handshake receive worker.
Session and keepalive are the enclosing driver's concrete callbacks; all native
checks, protocol sends, timer effects and counted releases are discharged here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
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

macro "entry_handshake_frame" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  repeat' first
    | (rx_retention_head createResponse; exact HandshakeFrames.create_response _ initial)
    | (rx_retention_head addMacToPacket; exact HandshakeFrames.add_mac _ _ initial)
    | (rx_retention_head timersHandshakeComplete; exact TimerFrames.handshake_complete _ _ initial)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact HandshakeFrames.sent _ initial)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact HandshakeFrames.received _ initial)
    | (rx_retention_head setPeerEndpointFromSkb; unfold setPeerEndpointFromSkb)
    | (rx_retention_head Cookies.loadPhase; exact TimerFrames.store Cookies.loadPhase_sameStore initial)
    | (rx_retention_head cookieValidatePacket; exact HandshakeFrames.cookie_frame (cookieValidatePacket_sameCookie _ _ _) initial)
    | (rx_retention_head WG.andM; unfold WG.andM)
    | (rx_retention_head WG.orM; unfold WG.orM)
    | entry_handshake_native_step initial))

open Lean Meta Elab Tactic in
elab "entry_checked_expand" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``SourcePassive.Checked do throwError "not an entry contract"
  evalTactic (← `(tactic| unfold SourcePassive.Checked StatePrefixPreserves))

open Lean Meta Elab Tactic in
elab "entry_callback_head " wanted:term : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do throwError "not an observer contract"
  let action := args[args.size - 2]!.consumeMData.headBeta
  let expected ← Lean.Elab.Term.elabTerm wanted none
  unless action.getAppFn == expected do throwError "different supplied callback"

macro "entry_handshake_step " safe:term " using " entry:term : tactic => `(tactic| first
  | entry_checked_expand
  | (maintenance_head CausalScope.scope; apply SourceEvents.scope $safe $entry)
  | (maintenance_head receiptWGObserved; refine SourceEvents.receipt $safe $entry _ _ ?_ (fun _ => rfl))
  | (maintenance_head HandshakeWorker.callback; apply SourceEvents.callback $safe $entry)
  | (maintenance_head HandshakeWorker.old; apply HandshakeObserved.old_call $safe $entry; solve | entry_handshake_frame)
  | (maintenance_head ProtocolSocket.observed; exact HandshakeObserved.protocol $safe $entry _ _)
  | (maintenance_head CookieSocket.observed; exact HandshakeObserved.cookie $safe $entry _ _ _)
  | (maintenance_head NestedPeerRelease.admitInitiationWith; exact ConsumerObserved.initiation $safe $entry _)
  | (maintenance_head NestedPeerRelease.admitResponseWith; exact ConsumerObserved.response $safe $entry _)
  | (maintenance_head NestedPeerRelease.cookieObserved; exact ConsumerObserved.cookie $safe $entry _)
  | (maintenance_head TimerEffects.derivedWith; exact HandshakeObserved.derived $safe $entry _)
  | (maintenance_head TimerEffects.traversalWith; exact HandshakeObserved.traversal $safe $entry _)
  | (maintenance_head StagedDisposal.Decoration.release; exact Source.release _ $safe $entry)
  | (maintenance_head captureWGRun;
     apply StatePrefixPreserves.captureWGObserved
     exact SourcePassive.native $safe $entry _ (by entry_handshake_frame))
  | (maintenance_head liftWGPrefix; exact SourcePassive.native $safe $entry _ (by entry_handshake_frame))
  | (maintenance_head Pure.pure; exact pure_checked $safe $entry _)
  | (maintenance_head ite; apply choice)
  | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ => Source.Carrier _ _))
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_intro
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
variable (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
variable (sessions : ∀ pid, Checked debts locals Safe (session pid))
variable (keepalives : ∀ pid, Checked debts locals Safe (keepalive pid))

def make (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (mac : HandshakeMac) : Ops (WGPrefix Event) :=
  HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
    (ExchangeJoint.receiveOps Event.exchange
      (HandshakeEffects.withEffects (receiveOps session keepalive mac)
        (Event.old ∘ Journal.Event.handshake) effects))

include entrySafe sessions keepalives

omit keepalives in
theorem response_source (mac : HandshakeMac) (pid : PeerId) :
    Checked debts locals Safe (responseWith (make session keepalive mac) pid) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold responseWith make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (entry_callback_head session; exact sessions _)
    | entry_handshake_step Safe using entrySafe

theorem after_mac (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Checked debts locals Safe (afterMacWith (make session keepalive mac) msg src loaded state) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold afterMacWith make
  simp only [HandshakeEffects.scopeOps,ExchangeJoint.receiveOps,HandshakeEffects.withEffects,
    CausalJournal.receiveOps,StagedDisposal.Decoration.receive,ProtocolSender.receiveOps,HandshakeWorker.observedOps]
  repeat' first
    | (maintenance_head responseWith; exact response_source Safe entrySafe session keepalive sessions _ _)
    | (entry_callback_head session; exact sessions _)
    | (entry_callback_head keepalive; exact keepalives _)
    | entry_handshake_step Safe using entrySafe

theorem receive (msg : Key) (src : SkbSource) : Checked debts locals Safe
    (CookieConsumption.receiveWith
      (NestedPeerRelease.cookieObserved ConsumerSource.nested Event.cookieConsumed)
      (make session keepalive) msg src) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold CookieConsumption.receiveWith
  repeat' first
    | (maintenance_head afterMacWith; exact after_mac Safe entrySafe session keepalive sessions keepalives _ _ _ _ _)
    | entry_handshake_step Safe using entrySafe

theorem worker : Checked debts locals Safe (CausalJournal.handshake session keepalive) := by
  change StatePrefixEnsures (Source.Carrier debts locals) Safe _ (fun _ => Source.Carrier debts locals)
  unfold CausalJournal.handshake CookieConsumption.workerWith HandshakeWorker.workerWith
  repeat' first
    | (maintenance_head CookieConsumption.receiveWith; exact receive Safe entrySafe session keepalive sessions keepalives _ _)
    | entry_handshake_step Safe using entrySafe

omit sessions in
theorem session_worker : Checked debts locals Safe (CausalJournal.handshake CausalJournal.session keepalive) :=
  worker Safe entrySafe CausalJournal.session keepalive (HandshakeObserved.session Safe entrySafe) keepalives

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeEntry
