import Leanux.Proofs.WG.Config.PeerGetterModel
import Leanux.Proofs.WG.Config.PeerPagePlanClaims
import Leanux.Proofs.WG.Config.PeerPageCoalesceClaims
import Leanux.Proofs.WG.Config.MultiPeerGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Pure message-plan normalization by the actual coalescer. No capacity,
head-fit, reference, freshness or successful producer premise is required. -/
theorem coalesce_peerGetterMessages (d : Device) (peers : PeerId → Peer) :
    coalesce (peerGetterMessages d peers) = pure (.ok (multiPeerJson d peers)) := by
  cases members : d.peerList with
  | nil =>
    have attrs : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
    simp [peerGetterMessages,members,peerPagePrefix,peerTailPages,coalesce,
      attrs,multiPeerJson,multiPeerParts]
  | cons pid ids =>
    have listed : d.peerList.isEmpty = false := by rw [members]; rfl
    let first := peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
    have split := peerPagePrefix_spec peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
    have flatten := (peerTailPages_spec peers (NLMSG_GOODSIZE-24) (by decide) first.2).1
    have ordered : first.1 ++ (peerTailPages peers (NLMSG_GOODSIZE-24) first.2).flatten = d.peerList := by
      rw [flatten]
      exact split.1
    simp only [peerGetterMessages,listed,Bool.false_eq_true,ite_false]
    rw [coalesce_complete_pages]
    change (pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
      (((multiPeerParts peers (first.1 ++ (peerTailPages peers (NLMSG_GOODSIZE-24) first.2).flatten)).map peerDumpWithIps).toArray.map
        fun p => Json.mkObj p.attrs))]))) : WG.M (Except Int Json)) = _
    rw [ordered]
    rfl

/-- When the first page completes, the plan count is precisely its one- or
 two-receive DONE-room budget. This is a static plan equality. -/
theorem peerPageReceiveCount_first_complete (d : Device) (peers : PeerId → Peer)
    (complete : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 = []) :
    peerPageReceiveCount peers d d.peerList =
      if (peerFirstCall d peers).skb.room < nlmsgTotal 4 then 2 else 1 := by
  simp [peerPageReceiveCount,peerPageFinalRoom,peerPages,complete,peerTailPages,
    List.getLastD,peerFirstCall] <;> split <;> omega

/-- A nonfinal first DATA adds one to the resumed plan's DATA-plus-spill
budget. It does not assert instrumented minimal receive execution. -/
theorem peerPageReceiveCount_first_more (d : Device) (peers : PeerId → Peer)
    (more : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ []) :
    peerPageReceiveCount peers d d.peerList =
      peerTailReceiveCount peers (peerTailPages peers (NLMSG_GOODSIZE-24)
        (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2) + 1 := by
  have nonempty : peerTailPages peers (NLMSG_GOODSIZE-24)
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [] := by
    cases rest : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 with
    | nil => exact False.elim (more rest)
    | cons id ids => simp [peerTailPages]
  obtain ⟨page,pages,tail⟩ := List.exists_cons_of_ne_nil nonempty
  simp [peerPageReceiveCount,peerPageFinalRoom,peerPages,tail,peerTailReceiveCount,List.getLastD]
  omega

/-- Only the actual first nonfinal page boundary supplies cursor lifetime data;
no final-page peer is constrained by this extraction. -/
theorem peerPageCursorData_first (d : Device) (peers : PeerId → Peer)
    (data : PeerPageCursorData peers (peerPages peers d d.peerList))
    (cursor : PeerId)
    (more : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [])
    (last : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1.getLast? = some cursor) :
    (peers cursor).isDead = false ∧ 0 < (peers cursor).refcount ∧ (peers cursor).refcount+1 < 2^31 := by
  have nonempty : peerTailPages peers (NLMSG_GOODSIZE-24)
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [] := by
    cases rest : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 with
    | nil => exact False.elim (more rest)
    | cons id ids => simp [peerTailPages]
  obtain ⟨page,pages,tail⟩ := List.exists_cons_of_ne_nil nonempty
  rw [peerPages,tail] at data
  exact data.1 cursor last

end Leanux.Proofs.WG.Config
