import Leanux.Proofs.WG.RetirementSecurity.HolderDumpSocket

/-! Stepped and bounded full dump callers preserve the exact key account.
The actual source chooses each replacement cursor; no initial empty cursor
or successful dump-completion condition is imposed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders NetlinkDump

theorem receive_keys (fd : Nat) (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((netlinkRecvmsg fd).run w).run a=.ok ((result,v),b)) : HolderAccount temporary v := by
  unfold netlinkRecvmsg at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a)=Except.ok ((sock,read),ar) at getter
  cases getter
  cases queue:(socketAt fd w).queue with
  | nil=>simp only [queue] at rest; cases rest; exact keys
  | cons skb remaining=>
    simp only [queue,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,written,aw,write,read,readState,ar,getter,rest⟩ := rest
    cases write
    let popped : NlSock := {socketAt fd w with queue:=remaining}
    have credit := socket_write_funded funded stable fd popped rfl
    change Except.ok ((socketAt fd (writeSocket fd popped w),writeSocket fd popped w),a)=
      Except.ok ((read,readState),ar) at getter
    cases getter
    split at rest
    · rename_i active
      rw [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,finished,af,finish,ret⟩ := rest
      cases u
      cases ret
      exact netlink_keys fd credit.1 credit.2 active (socket_keys keys fd popped)
        (socket_anchors anchors fd popped) a b finish
    · cases rest; exact socket_keys keys _ _

theorem start_keys (fd : Nat) (ref : DeviceRef)
    (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((netlinkDumpStart fd ref).run w).run a=.ok (((),v),b)) : HolderAccount temporary v := by
  unfold netlinkDumpStart at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a)=Except.ok ((sock,read),ar) at getter
  cases getter
  split at rest
  · cases rest
  · rename_i inactive
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨lookup,looked,al,looking,rest⟩ := rest
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp (lookupInterface_sameWGWorld ref) w a lookup looked al looking
    change looked=w at same
    subst looked
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨flag,checked,ac,decision,rest⟩ := rest
    cases lookup with
    | error e=>
      obtain ⟨flagEq,stateEq⟩ := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g=>g=w) .getStartErr true) w al flag checked ac rfl decision
      subst flag
      subst checked
      simp only [ite_true] at rest
      change Except.ok (((),writeSocket fd {socketAt fd w with queue := (socketAt fd w).queue ++ [{messages:=[.error e]}], ctx:={}, prevSeq:=0} w),ac)=Except.ok (((),v),b) at rest
      cases rest
      exact socket_keys keys _ _
    | ok value=>
      obtain ⟨flagEq,stateEq⟩ := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g=>g=w) .getStartErr false) w al flag checked ac rfl decision
      subst flag
      subst checked
      cases value
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,started,as,start,tail⟩ := rest
      cases start
      let starting : NlSock := {socketAt fd w with cbRunning:=true, dumpDoneErrno:=INT_MAX, prevSeq:=0, ctx:={hasWg:=true}}
      have credit := socket_write_funded funded stable fd starting (by simp [starting,activeCursor,inactive])
      exact netlink_keys fd credit.1 credit.2 (by rw [socketAt_write])
        (socket_keys keys fd starting) (socket_anchors anchors fd starting) ac b tail

macro "holder_dump_anchor_step" : tactic => `(tactic| first
  | (rx_retention_head netlinkDump; exact netlink_anchors _)
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp _)
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp _)
  | (rx_retention_head setNlSock; exact dump_anchors (setNlSock_sameDump _ _))
  | slot_anchor_step)

theorem receive_anchors (fd : Nat) : Preserves (SlotPeerReferences holders loans) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' holder_dump_anchor_step

theorem start_anchors (fd : Nat) (ref : DeviceRef) :
    Preserves (SlotPeerReferences holders loans) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config:={zeta:=false}) only [branch,invariant,unsupported]
  repeat' holder_dump_anchor_step

def During (holders : DurableHolders) (fd : Nat) (carriers : Ledger)
    (loans : Reservations) (temporary : Credits.Ledger) (w : WGWorld) : Prop :=
  DuringDump holders fd carriers loans w ∧ HolderAccount temporary w ∧ SlotPeerReferences holders loans w

theorem start (holders : DurableHolders) (fd : Nat) (ref : DeviceRef) :
    Preserves (During holders fd carriers loans temporary) (netlinkDumpStart fd ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases result
  obtain ⟨old,funded,stable⟩ := entry.1
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (netlinkDumpStart_during holders fd ref) w a () v b entry.1 run,
    start_keys fd ref funded stable entry.2.1 (cursor_anchors entry.2.2 fd old) a b run,
    (hoare_iff_run_ambient _ _ _).mp (start_anchors fd ref) w a () v b entry.2.2 run⟩

theorem receive (holders : DurableHolders) (fd : Nat) :
    Preserves (During holders fd carriers loans temporary) (netlinkRecvmsg fd) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  obtain ⟨old,funded,stable⟩ := entry.1
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (netlinkRecvmsg_during holders fd) w a result v b entry.1 run,
    receive_keys fd funded stable entry.2.1 (cursor_anchors entry.2.2 fd old) a b run,
    (hoare_iff_run_ambient _ _ _).mp (receive_anchors fd) w a result v b entry.2.2 run⟩

theorem device (holders : DurableHolders) (ref : DeviceRef) :
    Preserves (During holders 7 carriers loans temporary) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config:={zeta:=false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact start holders _ _)
    | (rx_retention_head netlinkRecvmsg; exact receive holders _)
    | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (During holders 7 carriers loans temporary))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (During holders 7 carriers loans temporary)
       intro x b
       change Preserves (During holders 7 carriers loans temporary) _)
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.HolderDump
