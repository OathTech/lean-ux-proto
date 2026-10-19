import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpSocket

/-! Whole and stepped native dump callers transport one exact account. The
fixed noncursor holders, RX carriers and caller loans remain unchanged; only
the actual selected socket cursor is exchanged. These are normal endpoint
contracts needed by the initialized runner, not a claim that it is closed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders NetlinkDump
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def During (holders : DurableHolders) (fd : Nat) (carriers : RxCredits.Ledger)
    (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ next : Option Owner, Account (holders.withCursor fd next) carriers loans w

theorem during_initial (account : Account holders carriers loans w) (fd : Nat) :
    During holders fd carriers loans w :=
  ⟨holders.cursorAt fd,by simpa only [withCursor_current] using account⟩

theorem start_during (holders : DurableHolders) (fd : Nat) (ref : DeviceRef) :
    Preserves (During holders fd carriers loans) (netlinkDumpStart fd ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨old,account⟩ := before
  cases value
  obtain ⟨next,kept⟩ := start fd ref account a b run
  exact ⟨next,by simpa only [withCursor_twice] using kept⟩

theorem receive_during (holders : DurableHolders) (fd : Nat) :
    Preserves (During holders fd carriers loans) (netlinkRecvmsg fd) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨old,account⟩ := before
  obtain ⟨next,kept⟩ := receive fd account a b run
  exact ⟨next,by simpa only [withCursor_twice] using kept⟩

theorem device_during (holders : DurableHolders) (ref : DeviceRef) :
    Preserves (During holders 7 carriers loans) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact start_during holders _ _)
    | (rx_retention_head netlinkRecvmsg; exact receive_during holders _)
    | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (During holders 7 carriers loans))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (During holders 7 carriers loans)
       intro _ _
       change Preserves (During holders 7 carriers loans) _)
    | rx_retention_step

/-- The original bounded whole-dump loop preserves a single exact cursor
account on normal return, including errno; completion is not assumed. -/
theorem device (ref : DeviceRef) (account : Account holders carriers loans w) (a b : Ambient)
    (run : ((wgGetDevice ref).run w).run a = .ok ((result,v),b)) :
    During holders 7 carriers loans v :=
  (hoare_iff_run_ambient _ _ _).mp (device_during holders ref)
    w a result v b (during_initial account 7) run

theorem boundary_start (fd : Nat) (ref : DeviceRef) :
    Preserves (ExactBoundary carriers loans) (netlinkDumpStart fd ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨holders,account⟩ := before
  cases value
  obtain ⟨next,kept⟩ := start fd ref account a b run
  exact ⟨holders.withCursor fd next,kept⟩

theorem boundary_receive (fd : Nat) :
    Preserves (ExactBoundary carriers loans) (netlinkRecvmsg fd) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨next,kept⟩ := receive fd account a b run
  exact ⟨holders.withCursor fd next,kept⟩

theorem boundary_device (ref : DeviceRef) :
    Preserves (ExactBoundary carriers loans) (wgGetDevice ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨next,kept⟩ := device ref account a b run
  exact ⟨holders.withCursor 7 next,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
