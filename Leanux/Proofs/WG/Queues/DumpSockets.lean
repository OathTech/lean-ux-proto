import Leanux.Proofs.WG.Queues.DumpSerialization
import Leanux.Proofs.WG.Queues.HolderWorkFrames

/-! Active dump socket cursor accounting. A saved cursor is counted once,
first as the stored holder and then as the actual callback's transient loan.
Publication installs only the new source-funded cursor; completion pays it
before deactivating the socket. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.NetlinkDump

def socketAt (fd : Nat) (w : WGWorld) : NlSock :=
  if fd == 8 then w.nlSock8 else w.nlSock7

def writeSocket (fd : Nat) (sock : NlSock) (w : WGWorld) : WGWorld :=
  if fd == 8 then {w with nlSock8 := sock} else {w with nlSock7 := sock}

def cursorAt (h : DurableHolders) (fd : Nat) : Option Owner :=
  if fd == 8 then h.cursor8 else h.cursor7

def withCursor (h : DurableHolders) (fd : Nat) (next : Option Owner) : DurableHolders :=
  if fd == 8 then {h with cursor8 := next} else {h with cursor7 := next}

def outsideCursor (h : DurableHolders) (fd : Nat) (loans : Reservations) : Reservations :=
  (h.withCursor fd none).owners ++ loans

theorem cursor_owners_perm (h : DurableHolders) (fd : Nat) (next : Option Owner)
    (loans : Reservations) :
    ((h.withCursor fd next).owners ++ loans).Perm (next.toList ++ outsideCursor h fd loans) := by
  apply List.perm_iff_count.mpr
  intro o
  by_cases hf : (fd == 8) = true
  all_goals simp [withCursor,outsideCursor,hf,owners,List.count_append]
  all_goals omega

theorem withCursor_current (h : DurableHolders) (fd : Nat) :
    h.withCursor fd (h.cursorAt fd) = h := by
  unfold withCursor cursorAt
  split <;> rfl

theorem Aligned.cursor_active {h : DurableHolders} (hi : h.Aligned w) (fd : Nat)
    (active : (socketAt fd w).cbRunning = true) :
    (h.cursorAt fd).map Owner.slot = (socketAt fd w).ctx.nextPeer := by
  by_cases hf : (fd == 8) = true
  · have ha : w.nlSock8.cbRunning = true := by simpa [socketAt,hf] using active
    simpa [cursorAt,socketAt,hf,activeCursor,ha] using hi.cursor8
  · have ha : w.nlSock7.cbRunning = true := by simpa [socketAt,hf] using active
    simpa [cursorAt,socketAt,hf,activeCursor,ha] using hi.cursor7

theorem Aligned.write_cursor {h : DurableHolders} (hi : h.Aligned w) (fd : Nat) (sock : NlSock)
    (next : Option Owner) (cursor : next.map Owner.slot = activeCursor sock) :
    (h.withCursor fd next).Aligned (writeSocket fd sock w) := by
  by_cases hf : (fd == 8) = true
  all_goals simp only [withCursor,writeSocket,hf,Bool.false_eq_true,ite_true,ite_false]
  · exact ⟨hi.base,hi.send,hi.clear,hi.tx,hi.cursor7,cursor⟩
  · exact ⟨hi.base,hi.send,hi.clear,hi.tx,cursor,hi.cursor8⟩

theorem cursor_input (hi : h.Funded cs loans w) (stable : StableRx cs w) (fd : Nat) :
    ClearWork.Inv cs ((h.cursorAt fd).toList ++ outsideCursor h fd loans) w := by
  refine ⟨WorkReservations.carrier_loans_perm hi.carriers ?_,stable⟩
  simpa only [withCursor_current] using cursor_owners_perm h fd (h.cursorAt fd) loans

theorem cursor_publish (aligned : h.Aligned w) (fd : Nat) (sock : NlSock) (next : Option Owner)
    (cursor : next.map Owner.slot = activeCursor sock)
    (funded : ClearWork.Inv cs (next.toList ++ outsideCursor h fd loans) w) :
    (h.withCursor fd next).Funded cs loans (writeSocket fd sock w) ∧
      StableRx cs (writeSocket fd sock w) := by
  have carrier : CarrierState cs (next.toList ++ outsideCursor h fd loans) (writeSocket fd sock w) :=
    funded.1.view (by unfold writeSocket; split <;> rfl)
  exact ⟨⟨aligned.write_cursor fd sock next cursor,
    WorkReservations.carrier_loans_perm carrier (cursor_owners_perm h fd next loans).symm⟩,
    funded.2.view (by unfold writeSocket; split <;> rfl)⟩

private theorem identity_frame {α : Type} {action : WG.M α}
    (ha : SameView (id : WGWorld → WGWorld) action) (initial : WGWorld) :
    Preserves (Frame initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp ha w a x v b run
  change v = w at same
  subst v
  exact hi

private theorem store_frame {α : Type} {action : WG.M α}
    (ha : SameWGStore action) (initial : WGWorld) : Preserves (Frame initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.trans (Frame.of_store ((ProjectedAction.iff_run_ambient _ _ _).mp ha w a x v b run))

theorem dump_peerGet_frame (pid : PeerId) (initial : WGWorld) :
    Preserves (Frame initial) (peerGet pid) := by
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' holder_work_step initial

theorem dump_done_frame (ctx : DumpCtx) (initial : WGWorld) :
    Preserves (Frame initial) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .getDoneHasWg ctx.hasWg) _)
    (fun _ => HolderWorkFrames.peerPut_frame _ initial)

private theorem dump_replace_frame (ctx : DumpCtx) (next : Option PeerId) (done : Bool)
    (initial : WGWorld) : Preserves (Frame initial) (DumpReservation.replaceSource ctx next done) := by
  unfold DumpReservation.replaceSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerGet; exact dump_peerGet_frame _ initial)
    | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ initial)
    | holder_work_step initial

private theorem dump_finish_frame (seq : Nat) (ctx : DumpCtx) (next : Option PeerId) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (done : Bool)
    (peers : Option (Array PeerDumpAttrs)) (initial : WGWorld) :
    Preserves (Frame initial) (DumpReservation.finishSource seq ctx next skb flags attrs done peers) := by
  unfold DumpReservation.finishSource
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head DumpReservation.replaceSource; exact dump_replace_frame _ _ _ initial)
    | holder_work_step initial

private theorem dump_tail_frame (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (initial : WGWorld) :
    Preserves (Frame initial) (deviceDumpTailSource d ctx skb flags attrs) := by
  rw [DumpReservation.tail_factor]
  exact preserves_bind (identity_frame (DumpReservation.walk_frame _ _ _) initial)
    (fun r => dump_finish_frame _ _ _ _ _ _ _ _ initial)

theorem dump_callback_frame (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) (initial : WGWorld) :
    Preserves (Frame initial) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  apply preserves_bind (store_frame getDev_sameWGStore initial)
  intro d
  apply preserves_bind (store_frame (deviceDumpHeader_sameWGStore d ctx seq skb) initial)
  intro r
  exact dump_tail_frame _ _ _ _ _ initial

theorem withCursor_twice (h : DurableHolders) (fd : Nat) (old next : Option Owner) :
    (h.withCursor fd old).withCursor fd next = h.withCursor fd next := by
  unfold withCursor
  split <;> rfl

theorem outside_replace (h : DurableHolders) (fd : Nat) (next : Option Owner) (loans : Reservations) :
    outsideCursor (h.withCursor fd next) fd loans = outsideCursor h fd loans := by
  simp only [outsideCursor,withCursor_twice]

/-- Literal suffix of netlink_dump after its optional WireGuard callback. -/
def socketTailSource (fd : Nat) (sock : NlSock) (skb0 : NlSkb) : WG.M Unit := do
  if sock.dumpDoneErrno > 0 || skb0.room < nlmsgTotal 4 then
    setNlSock fd {sock with queue := sock.queue ++ [skb0]}
    return
  let skb := {skb0 with room := skb0.room - nlmsgTotal 4, messages := skb0.messages ++ [.done 2 sock.dumpDoneErrno]}
  setNlSock fd {sock with queue := sock.queue ++ [skb]}
  wgGetDeviceDone sock.ctx
  let after ← getNlSock fd
  setNlSock fd {after with cbRunning := false}

theorem netlink_factor (fd : Nat) : netlinkDump fd = (do
    let sock ← getNlSock fd
    if sock.dumpDoneErrno > 0 then
      let r ← wgGetDeviceDump sock.ctx sock.prevSeq {}
      socketTailSource fd {sock with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret} r.skb
    else socketTailSource fd sock {}) := by
  unfold netlinkDump socketTailSource
  apply congrArg
  funext sock
  split <;> rfl

/-- A live local cursor is either published as the new lasting holder, or
paid by the actual done callback before cbRunning is cleared. -/
theorem socket_tail_normal {h : DurableHolders} (fd : Nat) (sock : NlSock) (skb : NlSkb)
    (next : Option Owner) (active : sock.cbRunning = true)
    (cursor : sock.ctx.nextPeer = next.map Owner.slot)
    (aligned : h.Aligned w)
    (funded : ClearWork.Inv cs (next.toList ++ outsideCursor h fd loans) w)
    (a b : Ambient)
    (run : ((socketTailSource fd sock skb).run w).run a = .ok (((),v),b)) :
    ∃ final : Option Owner, (h.withCursor fd final).Funded cs loans v ∧ StableRx cs v := by
  unfold socketTailSource at run
  split at run
  · change Except.ok (((),writeSocket fd {sock with queue := sock.queue ++ [skb]} w),a) =
      Except.ok (((),v),b) at run
    cases run
    exact ⟨next,cursor_publish aligned fd _ next
      (by simp only [activeCursor,active,ite_true]; exact cursor.symm) funded⟩
  · rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨u,written,aw,hwrite,rest⟩ := run
    cases hwrite
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,paid,ap,hdone,rest⟩ := rest
    cases u
    let published : NlSock := {sock with queue := sock.queue ++ [{skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno]}]}
    have before := cursor_publish aligned fd published next
      (by simp only [published,activeCursor,active,ite_true]; exact cursor.symm) funded
    have debt : ClearWork.Inv cs (next.toList ++ outsideCursor h fd loans) (writeSocket fd published w) :=
      ⟨funded.1.view (by unfold writeSocket; split <;> rfl),funded.2.view (by unfold writeSocket; split <;> rfl)⟩
    have after := DumpReservation.done_normal sock.ctx next cursor debt a ap hdone
    have frame := (hoare_iff_run_ambient _ _ _).mp
      (dump_done_frame sock.ctx (writeSocket fd published w)) _ a () paid ap (Frame.refl _) hdone
    have alignedPaid := before.1.aligned.frame frame
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨read,readState,ar,hread,tail⟩ := rest
    change Except.ok ((socketAt fd paid,paid),ap) = Except.ok ((read,readState),ar) at hread
    cases hread
    change Except.ok (((),writeSocket fd {socketAt fd paid with cbRunning := false} paid),ap) =
      Except.ok (((),v),b) at tail
    cases tail
    have cleared : ClearWork.Inv cs ((none : Option Owner).toList ++
        outsideCursor (h.withCursor fd next) fd loans) paid := by
      simpa only [Option.toList_none,List.nil_append,outside_replace] using after
    have final := cursor_publish alignedPaid fd {socketAt fd paid with cbRunning := false} none rfl cleared
    refine ⟨none,?_⟩
    simpa only [withCursor_twice] using final

/-- Every normal active dump call replaces or pays exactly the selected
socket cursor, retaining all other holder occurrences and explicit loans. -/
theorem netlinkDump_funded {h : DurableHolders} (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (active : (socketAt fd w).cbRunning = true) (a b : Ambient)
    (run : ((netlinkDump fd).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  rw [netlink_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,hread,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at hread
  cases hread
  have cursor := (hi.aligned.cursor_active fd active).symm
  have initial := cursor_input hi stable fd
  split at rest
  · rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨r,middle,am,hcallback,tail⟩ := rest
    obtain ⟨next,matched,funded⟩ := DumpReservation.dump_normal
      (socketAt fd w).ctx (socketAt fd w).prevSeq {} (h.cursorAt fd)
      cursor initial a am hcallback
    have frame := (hoare_iff_run_ambient _ _ _).mp
      (dump_callback_frame (socketAt fd w).ctx (socketAt fd w).prevSeq {} w)
      w a r middle am (Frame.refl w) hcallback
    exact socket_tail_normal fd {socketAt fd w with ctx := r.ctx, prevSeq := r.prevSeq, dumpDoneErrno := r.ret} r.skb next active matched (hi.aligned.frame frame) funded am b tail
  · exact socket_tail_normal fd (socketAt fd w) {} (h.cursorAt fd) active cursor hi.aligned initial a b rest

/-- The existing lifetime observer uses that same actual normal endpoint.
No new observer or restriction on incoming history is introduced. -/
theorem netlinkDump_observed_funded {h : DurableHolders} (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (active : (socketAt fd w).cbRunning = true) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (netlinkDumpPrefix fd) w a history).1 = .ok (((),v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  exact netlinkDump_funded fd hi stable active a b
    ((netlinkDumpPrefix_erases fd w a history).symm.trans run)

theorem socketAt_write (fd : Nat) (sock : NlSock) (w : WGWorld) :
    socketAt fd (writeSocket fd sock w) = sock := by
  unfold socketAt writeSocket
  split <;> rfl

theorem Aligned.cursor_value {h : DurableHolders} (hi : h.Aligned w) (fd : Nat) :
    (h.cursorAt fd).map Owner.slot = activeCursor (socketAt fd w) := by
  by_cases hf : (fd == 8) = true
  · simpa [cursorAt,socketAt,hf] using hi.cursor8
  · simpa [cursorAt,socketAt,hf] using hi.cursor7

theorem socket_write_funded {h : DurableHolders} (hi : h.Funded cs loans w)
    (stable : StableRx cs w) (fd : Nat) (sock : NlSock)
    (same : activeCursor sock = activeCursor (socketAt fd w)) :
    h.Funded cs loans (writeSocket fd sock w) ∧ StableRx cs (writeSocket fd sock w) := by
  have published := cursor_publish hi.aligned fd sock (h.cursorAt fd)
    ((hi.aligned.cursor_value fd).trans same.symm) (cursor_input hi stable fd)
  simpa only [withCursor_current] using published

/-- Receiving a queued chunk keeps the current holder until the actual
cbRunning guard invokes netlink_dump. Empty queues and inactive sockets need
no cursor payment; all original socket IDs remain in the domain. -/
theorem netlinkRecvmsg_funded {h : DurableHolders} (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((netlinkRecvmsg fd).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  unfold netlinkRecvmsg at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,hread,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at hread
  cases hread
  cases hq : (socketAt fd w).queue with
  | nil =>
    simp only [hq] at rest
    cases rest
    exact ⟨h.cursorAt fd,by simpa only [withCursor_current] using And.intro hi stable⟩
  | cons skb queue =>
    simp only [hq,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,written,aw,hwrite,read,readState,ar,hread,rest⟩ := rest
    cases hwrite
    let popped : NlSock := {socketAt fd w with queue := queue}
    have kept := socket_write_funded hi stable fd popped rfl
    change Except.ok ((socketAt fd (writeSocket fd popped w),writeSocket fd popped w),a) =
      Except.ok ((read,readState),ar) at hread
    cases hread
    split at rest
    · rename_i active
      rw [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,finished,af,hfinish,ret⟩ := rest
      cases u
      cases ret
      exact netlinkDump_funded fd kept.1 kept.2 active a b hfinish
    · cases rest
      exact ⟨h.cursorAt fd,by simpa only [withCursor_current] using kept⟩

/-- Starting a dump first clears the old context. Busy sockets stop; lookup
errors publish only their actual acknowledgement, while successful starts
activate an empty cursor and enter the checked native dump call. -/
theorem netlinkDumpStart_funded {h : DurableHolders} (fd : Nat) (ref : DeviceRef)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((netlinkDumpStart fd ref).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  unfold netlinkDumpStart at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,hread,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at hread
  cases hread
  split at rest
  · cases rest
  · rename_i inactive
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨lookup,looked,al,hlookup,rest⟩ := rest
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp (lookupInterface_sameWGWorld ref)
      w a lookup looked al hlookup
    change looked = w at same
    subst looked
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨flag,checked,ac,hbranch,rest⟩ := rest
    cases lookup with
    | error e =>
      have decision := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g => g=w) .getStartErr true) w al flag checked ac rfl hbranch
      obtain ⟨flagEq,stateEq⟩ := decision
      subst flag
      subst checked
      simp only [ite_true] at rest
      change Except.ok (((),writeSocket fd {socketAt fd w with
        queue := (socketAt fd w).queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0} w),ac) =
        Except.ok (((),v),b) at rest
      cases rest
      have kept := socket_write_funded hi stable fd
        {socketAt fd w with queue := (socketAt fd w).queue ++ [{ messages := [.error e] }], ctx := {}, prevSeq := 0}
        (by simp [activeCursor,inactive])
      exact ⟨h.cursorAt fd,by simpa only [withCursor_current] using kept⟩
    | ok value =>
      have decision := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g => g=w) .getStartErr false) w al flag checked ac rfl hbranch
      obtain ⟨flagEq,stateEq⟩ := decision
      subst flag
      subst checked
      cases value
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,started,as,hstart,tail⟩ := rest
      cases hstart
      let starting : NlSock := {socketAt fd w with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := {hasWg := true}}
      have kept := socket_write_funded hi stable fd starting (by simp [starting,activeCursor,inactive])
      exact netlinkDump_funded fd kept.1 kept.2 (by rw [socketAt_write]) ac b tail

theorem netlinkRecvmsg_observed_funded {h : DurableHolders} (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (netlinkRecvmsgPrefix fd) w a history).1 = .ok ((result,v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  exact netlinkRecvmsg_funded fd hi stable a b
    ((netlinkRecvmsgPrefix_erases fd w a history).symm.trans run)

theorem netlinkDumpStart_observed_funded {h : DurableHolders} (fd : Nat) (ref : DeviceRef)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (history : List LifetimeEvent)
    (run : (runStatePrefix (netlinkDumpStartPrefix fd ref) w a history).1 = .ok (((),v),b)) :
    ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans v ∧ StableRx cs v := by
  exact netlinkDumpStart_funded fd ref hi stable a b
    ((netlinkDumpStartPrefix_erases fd ref w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
