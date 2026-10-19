import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHandshakeConsumers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSourceQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeObserved

/-! Logical-prefix extension of the original source contract.
Native silent-interval correspondence remains separate.

 Actual consumer, protocol and session receipts retain the paired ledger.
Passive protocol sockets have no data-ticket demand; counted consumer
repayments are composed through their actual source before these receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Handshake
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive Consumers NestedPeerRelease
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem initiation (mac : HandshakeMac) : Checked debts locals Safe
    (admitInitiationWith nested ConsumerObserved.admission mac) := by
  unfold admitInitiationWith
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved (initiation_check Safe accountSafe mac.input))
  intro checked
  dsimp only
  split
  · exact bind_checked Safe (emit Safe accountSafe _ rfl (fun _ => rfl))
      (fun _ => Passive.native Safe accountSafe _ (ConsumerFrames.initiation_continue _ _))
  · exact Passive.native Safe accountSafe _ (ConsumerFrames.initiation_continue _ _)

theorem response (mac : HandshakeMac) : Checked debts locals Safe
    (admitResponseWith nested ConsumerObserved.admission mac) := by
  unfold admitResponseWith
  apply bind_checked Safe (StatePrefixPreserves.captureWGObserved (response_check Safe accountSafe mac.input))
  intro checked
  dsimp only
  split
  · exact bind_checked Safe (emit Safe accountSafe _ rfl (fun _ => rfl))
      (fun _ => Passive.native Safe accountSafe _ (ConsumerFrames.response_continue _ _))
  · exact Passive.native Safe accountSafe _ (ConsumerFrames.response_continue _ _)

theorem cookie_consumed (msg : Key) : Checked debts locals Safe
    (NestedPeerRelease.cookieObserved nested Event.cookieConsumed msg) :=
  receipt Safe accountSafe _ _ (Consumers.cookie Safe accountSafe msg)
    (fun _ => rfl) (fun _ _ => rfl)

theorem protocol (pid : PeerId) (msg : Key) : Checked debts locals Safe
    (ProtocolSocket.observed Event.protocolSocket scope? pid msg) :=
  QuietSource.checked Safe accountSafe (ProtocolSocket.observed_erases _ _ _ _)
    (ProtocolSocket.observed_appends _ _ _ _)
    (ProtocolSocket.observed_frame SourceQuiet.birth? _ (fun _ => SourceQuiet.birth_none rfl) _ _ _)
    (ProtocolSocket.observed_frame CompleteQuiet.terminal? _
      (fun _ => CompleteQuiet.terminal_none (fun _ => rfl)) _ _ _)
    (HandshakeFrames.buffer pid msg)

theorem cookie (mac : HandshakeMac) (msg : Key) (src : SkbSource) : Checked debts locals Safe
    (CookieSocket.observed Event.cookieSocket mac msg src) :=
  QuietSource.checked Safe accountSafe (CookieSocket.observed_erases _ _ _ _)
    (CookieSocket.observed_appends _ _ _ _)
    (CookieSocket.observed_frame SourceQuiet.birth? _ (fun _ => SourceQuiet.birth_none rfl) _ _ _)
    (CookieSocket.observed_frame CompleteQuiet.terminal? _
      (fun _ => CompleteQuiet.terminal_none (fun _ => rfl)) _ _ _)
    (HandshakeFrames.cookie msg src)

theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (frame : SameView StagedEntry.view native) : Checked debts locals Safe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake?
      (HandshakeCausal.call kind pid native)) := by
  rw [HandshakeEffects.old_call]
  exact callback Safe accountSafe kind pid _ (Passive.native Safe accountSafe native frame)

theorem session (pid : PeerId) : Checked debts locals Safe (CausalJournal.session pid) := by
  unfold CausalJournal.session HandshakeSecurity.ExchangeJoint.session
  apply receipt Safe accountSafe
  · unfold state Journal.session HandshakeSecurity.Responder.DriverCuts.session
    rw [Staged.Origins.focused_native_receipt,Staged.Origins.focused_native_receipt]
    exact receipt Safe accountSafe _ _ (Passive.native Safe accountSafe _ (KeyFrames.session pid))
      (fun _ => rfl) (fun _ _ => rfl)
  · intro r; rfl
  · intro r position; rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Handshake
