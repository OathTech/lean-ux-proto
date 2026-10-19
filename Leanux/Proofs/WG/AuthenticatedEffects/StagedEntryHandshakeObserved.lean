import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySourceQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyObserved

/-! Actual passive protocol callbacks retain full entry accounting. The native
frames and event projection are independent premises discharged here; nested
consumer repayment instead uses its counted source contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal SourcePassive
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (entrySafe : ∀ ledger h w, Inv h ledger debts locals w → Safe h)
include entrySafe

theorem protocol (pid : PeerId) (msg : Key) : Checked debts locals Safe
    (ProtocolSocket.observed Event.protocolSocket scope? pid msg) :=
  SourceQuiet.checked Safe entrySafe (ProtocolSocket.observed_erases _ _ _ _)
    (ProtocolSocket.observed_appends _ _ _ _)
    (ProtocolSocket.observed_frame SourceQuiet.birth? _ (fun _ => SourceQuiet.birth_none rfl) _ _ _)
    (HandshakeFrames.buffer pid msg)

theorem cookie (mac : HandshakeMac) (msg : Key) (src : SkbSource) : Checked debts locals Safe
    (CookieSocket.observed Event.cookieSocket mac msg src) :=
  SourceQuiet.checked Safe entrySafe (CookieSocket.observed_erases _ _ _ _)
    (CookieSocket.observed_appends _ _ _ _)
    (CookieSocket.observed_frame SourceQuiet.birth? _ (fun _ => SourceQuiet.birth_none rfl) _ _ _)
    (HandshakeFrames.cookie msg src)

theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (frame : SameView StagedEntry.view native) : Checked debts locals Safe
    (HandshakeWorker.old (Event.old ∘ Journal.Event.handshake) handshake?
      (HandshakeCausal.call kind pid native)) := by
  rw [HandshakeEffects.old_call]
  exact SourceEvents.callback Safe entrySafe kind pid _ (SourcePassive.native Safe entrySafe native frame)

theorem session (pid : PeerId) : Checked debts locals Safe (CausalJournal.session pid) :=
  fixed Safe entrySafe (fun _ => KeyObserved.session pid)

theorem derived (pid : PeerId) : Checked debts locals Safe (TimerEffects.derivedWith effects pid) :=
  fixed Safe entrySafe (fun _ => TimerObserved.derived pid)

theorem traversal (pid : PeerId) : Checked debts locals Safe (TimerEffects.traversalWith effects pid) :=
  fixed Safe entrySafe (fun _ => TimerObserved.traversal pid)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.HandshakeObserved
