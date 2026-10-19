import Leanux.Proofs.WG.RetirementSecurity.HolderDumpChunks

/-! Actual netlink socket publication and completion exchange only their
cursor peer loan. Independent key-slot anchors are retained while completion
pays its selected cursor, including the last peer reference of a dead peer. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders NetlinkDump

theorem cursor_anchors (entry : SlotPeerReferences holders loans w) (fd : Nat) (next : Option Owner) :
    SlotPeerReferences (holders.withCursor fd next) loans w := by
  apply entry.rename
  unfold withCursor
  split <;> rfl

theorem socket_keys (keys : HolderAccount temporary w) (fd : Nat) (sock : NlSock) :
    HolderAccount temporary (writeSocket fd sock w) := by
  apply keys.points
  unfold writeSocket
  split <;> rfl

theorem socket_anchors (entry : SlotPeerReferences holders loans w) (fd : Nat) (sock : NlSock) :
    SlotPeerReferences holders loans (writeSocket fd sock w) := by
  unfold writeSocket
  split <;> exact entry

theorem tail_socket_keys (fd : Nat) (sock : NlSock) (skb : NlSkb) (next : Option Owner)
    (cursor : sock.ctx.nextPeer=next.map Owner.slot)
    (funded : ClearWork.Inv carriers (next.toList ++ outsideCursor holders fd loans) w)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((socketTailSource fd sock skb).run w).run a=.ok (((),v),b)) :
    HolderAccount temporary v := by
  unfold socketTailSource at run
  split at run
  · change Except.ok (((),writeSocket fd {sock with queue:=sock.queue++[skb]} w),a)=Except.ok (((),v),b) at run
    cases run
    exact socket_keys keys _ _
  · rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨u,written,aw,write,rest⟩ := run
    cases write
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨u,paid,ap,done,rest⟩ := rest
    cases u
    let published : NlSock := {sock with queue := sock.queue ++ [{skb with room := skb.room - nlmsgTotal 4, messages := skb.messages ++ [.done 2 sock.dumpDoneErrno]}]}
    have credit : ClearWork.Inv carriers
        (next.toList ++ ((holders.withCursor fd none).owners ++ loans)) (writeSocket fd published w) :=
      ⟨funded.1.view (by unfold writeSocket; split <;> rfl),funded.2.view (by unfold writeSocket; split <;> rfl)⟩
    have after := done_keys sock.ctx next cursor credit (socket_keys keys fd published)
      (socket_anchors (cursor_anchors anchors fd none) fd published) a ap done
    rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨read,readState,ar,getter,tail⟩ := rest
    change Except.ok ((socketAt fd paid,paid),ap)=Except.ok ((read,readState),ar) at getter
    cases getter
    change Except.ok (((),writeSocket fd {socketAt fd paid with cbRunning:=false} paid),ap)=Except.ok (((),v),b) at tail
    cases tail
    exact socket_keys after _ _

theorem netlink_keys (fd : Nat) (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (active : (socketAt fd w).cbRunning=true)
    (keys : HolderAccount temporary w) (anchors : SlotPeerReferences holders loans w)
    (a b : Ambient)
    (run : ((netlinkDump fd).run w).run a=.ok (((),v),b)) : HolderAccount temporary v := by
  rw [netlink_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨sock,read,ar,getter,rest⟩ := run
  change Except.ok ((socketAt fd w,w),a)=Except.ok ((sock,read),ar) at getter
  cases getter
  have cursor := (funded.aligned.cursor_active fd active).symm
  have credit := cursor_input funded stable fd
  split at rest
  · rw [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨r,middle,am,callback,tail⟩ := rest
    obtain ⟨next,matched,after⟩ := DumpReservation.dump_normal
      (socketAt fd w).ctx (socketAt fd w).prevSeq {} (holders.cursorAt fd) cursor credit a am callback
    have account := chunk_keys _ _ _ (holders.cursorAt fd) cursor credit keys
      (cursor_anchors anchors fd none) a am callback
    have retained := (hoare_iff_run_ambient _ _ _).mp (chunk_anchors _ _ _)
      w a r middle am anchors callback
    exact tail_socket_keys fd _ _ next matched after account retained am b tail
  · exact tail_socket_keys fd _ _ (holders.cursorAt fd) cursor credit keys anchors a b rest

theorem dump_anchors {action : WG.M α} (same : SameDump action) :
    Preserves (SlotPeerReferences holders loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  have device : v.dev=w.dev := congrArg WGStoreView.dev
    ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)
  simpa only [SlotPeerReferences,device] using entry

theorem netlink_anchors (fd : Nat) : Preserves (SlotPeerReferences holders loans) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact chunk_anchors _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact done_anchors _)
    | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (SlotPeerReferences holders loans))
    | (rx_retention_head setNlSock; exact dump_anchors (setNlSock_sameDump _ _))
    | slot_anchor_step

end Leanux.Proofs.WG.RetirementSecurity.HolderDump
