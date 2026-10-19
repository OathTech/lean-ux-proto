import Leanux.Proofs.WG.Config.MixedPageSelectionClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

theorem mixedBoundary_fresh_of_nodup (d : Device) (peers : PeerId → Peer)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (position : MixedPeerPosition d rows cursor) (suffix : MixedRowsSuffix peers rows ctx)
    (distinct : d.peerList.Nodup)
    (nodeDistinct : ∀pid ∈ d.peerList,(peers pid).allowedipsList.Nodup) :
    MixedBoundaryFresh d peers rows ctx cursor := by
  constructor
  · intro old selected
    subst cursor
    obtain ⟨before,members⟩ := position
    have size : (before ++ old :: rows.map Prod.fst).length-rows.length-1=before.length := by
      simp only [List.length_append,List.length_cons,List.length_map]
      omega
    rw [members,size]
    simp only [List.take_left]
    rw [members] at distinct
    exact fun member=>(List.pairwise_append.mp distinct).2.2 old member old (by simp) rfl
  · intro pid ids tail start selected next
    have member := (mixedOrigin_members d peers rows ctx cursor position suffix
      (pid,ids) (by rw [selected]; exact List.mem_cons_self)).1
    rw [selected] at suffix
    have first := suffix.1
    rw [next] at first
    obtain ⟨head,before,members⟩ := first
    have fresh := nodeDistinct pid member
    have size : (before++ids).length-ids.length=before.length := by simp
    rw [members,size]
    simp only [List.take_left]
    rw [members] at fresh
    have inIds : start ∈ ids := List.mem_of_mem_head? head
    exact fun inside=>(List.pairwise_append.mp fresh).2.2 start inside start inIds rfl

theorem mixedPages_fresh_of_nodup (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) {hasWg:=true})
    (distinct : d.peerList.Nodup)
    (nodeDistinct : ∀pid ∈ d.peerList,(peers pid).allowedipsList.Nodup) :
    MixedPlanFresh d peers
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg:=true} ready) := by
  intro page member
  have start := mixedInitialRows_origin d peers {hasWg:=true} rfl
  have origin := mixedPages_origin d peers nodes (mixedInitialRows d peers) {hasWg:=true}
    ready start.1 start.2 page (List.dropLast_subset _ member)
  exact mixedBoundary_fresh_of_nodup d peers page.remaining page.native.1
    page.native.2.1 origin.1 origin.2 distinct nodeDistinct

end Leanux.Proofs.WG.Config
