import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCursor

/-! Native dump socket publication retains the lower and upper account on
one actual cursor witness. Completion pays that cursor before deactivation;
an unfinished chunk publishes the acquired occurrence as its durable holder. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders NetlinkDump
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem Credits.socket (account : Credits carriers loans w) (fd : Nat) (sock : NlSock) :
    Credits carriers loans (writeSocket fd sock w) := by
  refine ⟨⟨account.lower.1.view ?_,account.lower.2.view ?_⟩,account.upper.peer_view ?_⟩
  all_goals unfold writeSocket; split <;> rfl

theorem socket_tail (fd : Nat) (sock : NlSock) (skb : NlSkb) (next : Option Owner)
    (active : sock.cbRunning = true) (cursor : sock.ctx.nextPeer = next.map Owner.slot)
    (aligned : holders.Aligned w)
    (account : Credits carriers (next.toList ++ outsideCursor holders fd loans) w)
    (a b : Ambient) (run : ((socketTailSource fd sock skb).run w).run a = .ok (((),v),b)) :
    ∃ final : Option Owner, Account (holders.withCursor fd final) carriers loans v := by
  unfold socketTailSource at run
  split at run
  · change Except.ok (((),writeSocket fd {sock with queue := sock.queue ++ [skb]} w),a) =
      Except.ok (((),v),b) at run
    cases run
    exact ⟨next,cursor_publish aligned fd _ next
      (by simp only [activeCursor,active,ite_true]; exact cursor.symm) account⟩
  · rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨u,written,aw,write,rest⟩ := run
    cases write
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,paid,ap,payment,rest⟩ := rest
    cases u
    let published : NlSock := {sock with queue := sock.queue ++
      [{skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno]}]}
    have before := cursor_publish aligned fd published next
      (by simp only [published,activeCursor,active,ite_true]; exact cursor.symm) account
    have debt := account.socket fd published
    have after := done sock.ctx next cursor debt a ap payment
    have frame := (hoare_iff_run_ambient _ _ _).mp
      (dump_done_frame sock.ctx (writeSocket fd published w)) _ a () paid ap (Frame.refl _) payment
    have alignedPaid := before.funded.aligned.frame frame
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨read,readState,ar,getter,tail⟩ := rest
    change Except.ok ((socketAt fd paid,paid),ap) = Except.ok ((read,readState),ar) at getter
    cases getter
    change Except.ok (((),writeSocket fd {socketAt fd paid with cbRunning := false} paid),ap) =
      Except.ok (((),v),b) at tail
    cases tail
    have cleared : Credits carriers ((none : Option Owner).toList ++
        outsideCursor (holders.withCursor fd next) fd loans) paid := by
      simpa only [Option.toList_none,List.nil_append,outside_replace] using after
    have final := cursor_publish alignedPaid fd {socketAt fd paid with cbRunning := false} none rfl cleared
    exact ⟨none,by simpa only [withCursor_twice] using final⟩

/-- An actual active dump returns one replacement holder list shared by
Funded, the balance upper bound and StableRx. No cursor-distinctness is needed. -/
theorem netlink (fd : Nat) (account : Account holders carriers loans w)
    (active : (socketAt fd w).cbRunning = true) (a b : Ambient)
    (run : ((netlinkDump fd).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner, Account (holders.withCursor fd next) carriers loans v := by
  rw [netlink_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at getter
  cases getter
  have cursor := (account.funded.aligned.cursor_active fd active).symm
  have initial := cursor_input account fd
  split at rest
  · rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨r,middle,am,callback,tail⟩ := rest
    obtain ⟨next,matched,credit⟩ := chunk (socketAt fd w).ctx (socketAt fd w).prevSeq {}
      (holders.cursorAt fd) cursor initial a am callback
    have frame := (hoare_iff_run_ambient _ _ _).mp
      (dump_callback_frame (socketAt fd w).ctx (socketAt fd w).prevSeq {} w)
      w a r middle am (Frame.refl w) callback
    exact socket_tail fd {socketAt fd w with ctx := r.ctx,prevSeq := r.prevSeq,dumpDoneErrno := r.ret}
      r.skb next active matched (account.funded.aligned.frame frame) credit am b tail
  · exact socket_tail fd (socketAt fd w) {} (holders.cursorAt fd) active cursor
      account.funded.aligned initial a b rest

theorem socket_write (account : Account holders carriers loans w) (fd : Nat) (sock : NlSock)
    (same : activeCursor sock = activeCursor (socketAt fd w)) :
    Account holders carriers loans (writeSocket fd sock w) := by
  have kept := cursor_publish account.funded.aligned fd sock (holders.cursorAt fd)
    ((account.funded.aligned.cursor_value fd).trans same.symm) (cursor_input account fd)
  simpa only [withCursor_current] using kept

theorem receive (fd : Nat) (account : Account holders carriers loans w) (a b : Ambient)
    (run : ((netlinkRecvmsg fd).run w).run a = .ok ((result,v),b)) :
    ∃ next : Option Owner, Account (holders.withCursor fd next) carriers loans v := by
  unfold netlinkRecvmsg at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at getter
  cases getter
  cases queue : (socketAt fd w).queue with
  | nil =>
    simp only [queue] at rest
    cases rest
    exact ⟨holders.cursorAt fd,by simpa only [withCursor_current] using account⟩
  | cons skb remaining =>
    simp only [queue,MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,written,aw,write,read,readState,ar,getter,rest⟩ := rest
    cases write
    let popped : NlSock := {socketAt fd w with queue := remaining}
    have kept := socket_write account fd popped rfl
    change Except.ok ((socketAt fd (writeSocket fd popped w),writeSocket fd popped w),a) =
      Except.ok ((read,readState),ar) at getter
    cases getter
    split at rest
    · rename_i active
      rw [MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,finished,af,finish,ret⟩ := rest
      cases u
      cases ret
      exact netlink fd kept active a b finish
    · cases rest
      exact ⟨holders.cursorAt fd,by simpa only [withCursor_current] using kept⟩

theorem start (fd : Nat) (ref : DeviceRef) (account : Account holders carriers loans w) (a b : Ambient)
    (run : ((netlinkDumpStart fd ref).run w).run a = .ok (((),v),b)) :
    ∃ next : Option Owner, Account (holders.withCursor fd next) carriers loans v := by
  unfold netlinkDumpStart at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a) = Except.ok ((sock,read),ar) at getter
  cases getter
  split at rest
  · cases rest
  · rename_i inactive
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨lookup,looked,al,looking,rest⟩ := rest
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp (lookupInterface_sameWGWorld ref) w a lookup looked al looking
    change looked = w at same
    subst looked
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨flag,checked,ac,decision,rest⟩ := rest
    cases lookup with
    | error e =>
      obtain ⟨flagEq,stateEq⟩ := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g => g = w) .getStartErr true) w al flag checked ac rfl decision
      subst flag
      subst checked
      simp only [ite_true] at rest
      change Except.ok (((),writeSocket fd {socketAt fd w with queue := (socketAt fd w).queue ++ [{messages := [.error e]}],ctx := {},prevSeq := 0} w),ac) =
          Except.ok (((),v),b) at rest
      cases rest
      have kept := socket_write account fd
        {socketAt fd w with queue := (socketAt fd w).queue ++ [{messages := [.error e]}],ctx := {},prevSeq := 0}
        (by simp [activeCursor,inactive])
      exact ⟨holders.cursorAt fd,by simpa only [withCursor_current] using kept⟩
    | ok value =>
      obtain ⟨flagEq,stateEq⟩ := (hoare_iff_run_ambient _ _ _).mp
        (branch_predicate_native (fun g => g = w) .getStartErr false) w al flag checked ac rfl decision
      subst flag
      subst checked
      cases value
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at rest
      obtain ⟨u,started,as,start,tail⟩ := rest
      cases start
      let starting : NlSock := {socketAt fd w with cbRunning := true,dumpDoneErrno := INT_MAX, prevSeq := 0,ctx := {hasWg := true}}
      have kept := socket_write account fd starting (by simp [starting,activeCursor,inactive])
      exact netlink fd kept (by rw [socketAt_write]) ac b tail

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
