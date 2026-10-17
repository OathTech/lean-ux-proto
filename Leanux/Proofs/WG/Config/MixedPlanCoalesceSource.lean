import Leanux.Proofs.WG.Config.CoalesceMessageSource
import Leanux.Proofs.WG.Config.MixedCoalescePlanSource
import Leanux.Proofs.WG.Config.MixedPageTransportModel
import Leanux.Proofs.WG.Config.MixedPageSelectionModel
import Leanux.Proofs.WG.Config.MixedCallbackFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Prepared DATA pages accept absent or identical device headers and finish
at their actual DONE; inner coalescer errors remain in the native action. -/
theorem coalesce_prepared_tail (d : Device) (pages : List MixedPeerScan) (acc : Array PeerDumpAttrs)
    (nonempty : d.peerList.isEmpty = false) :
    (forIn ((pages.map (mixedPageMessage d)) ++ [.done 2 0])
      (some (deviceFixedAttrs d),acc,none) coalesceMessageStep) =
      (do
        let peers ← forIn pages acc mixedCoalescePage
        pure (some (deviceFixedAttrs d),peers,some 0) : WG.M _) := by
  induction pages generalizing acc with
  | nil => simp [coalesceMessageStep]
  | cons page pages ih =>
    have header : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
    cases phase : page.native.1.nextPeer <;>
      simp [mixedPageMessage,nonempty,phase,coalesceMessageStep,mixedCoalescePage,header,ih]

/-- Exact original DATA/DONE coalescing reduces to its actual peer fold once
the first DATA supplies the device header. No peer-fold success is assumed. -/
theorem coalesce_mixedPageMessages_source (d : Device) (page : MixedPeerScan) (pages : List MixedPeerScan)
    (nonempty : d.peerList.isEmpty = false) (fresh : page.native.1.nextPeer = none) :
    coalesce (mixedPageMessages d (page::pages)) =
      (do
        let acc ← forIn (page::pages) #[] mixedCoalescePage
        pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr (acc.map fun p => Json.mkObj p.attrs))])))) := by
  have header : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  have firstStep : coalesceMessageStep (mixedPageMessage d page) (none,#[],none) =
      (do
        let out ← forIn page.native.2.2.2.2.toList (#[],true) coalescePeerStep
        pure (.yield (some (deviceFixedAttrs d),out.1,none)) : WG.M _) := by
    simp [coalesceMessageStep,mixedPageMessage,fresh,nonempty,header]
  rw [coalesce_messages_source]
  change ((forIn (mixedPageMessage d page :: (pages.map (mixedPageMessage d) ++ [.done 2 0]))
    (none,#[],none) coalesceMessageStep) >>= coalesceFinish) = _
  rw [List.forIn_cons,firstStep]
  simp only [bind_assoc,pure_bind]
  simp only [coalesce_prepared_tail d pages _ nonempty]
  simp [coalesceFinish,mixedCoalescePage]

/-- Entire canonical mixed peer/AIP plan under the original coalescer. The
initial empty device retains its cancelled nest; all other pages preserve
ordered repeated peer/node occurrences and exact stored-width serialization. -/
theorem coalesce_mixedPages (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (ctx : DumpCtx) (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) ctx)
    (freshPeer : ctx.nextPeer = none) (freshAip : ctx.nextAllowedip = none) :
    coalesce (mixedPageMessages d (mixedPages d peers nodes (mixedInitialRows d peers) ctx ready)) =
      (pure (.ok (Json.mkObj (deviceFixedAttrs d ++ [("peers",Json.arr
        ((mixedRowsParts peers nodes ctx (mixedInitialRows d peers)).toArray.map
          fun p => Json.mkObj p.attrs))]))) : WG.M _) := by
  by_cases empty : d.peerList = []
  · simp [mixedPages,mixedInitialRows,empty,mixedPeerScan,mixedPageMessages,mixedPageMessage,
      freshPeer,coalesce,deviceFixedAttrs,mixedRowsParts]
  · have nonempty : d.peerList.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
    let page := mixedPeerScan d peers nodes (mixedInitialRows d peers) ctx ctx.nextPeer
      {room := mixedPageRoom d ctx} #[]
    have decomposition : ∃ tail, mixedPages d peers nodes (mixedInitialRows d peers) ctx ready = page::tail := by
      rw [mixedPages]
      dsimp only
      split
      · exact ⟨[],rfl⟩
      · exact ⟨_,rfl⟩
    obtain ⟨tail,eq⟩ := decomposition
    have header : page.native.1.nextPeer = none :=
      (mixedPeerScan_oldCursor d peers nodes (mixedInitialRows d peers) ctx ctx.nextPeer
        {room := mixedPageRoom d ctx} #[]).trans freshPeer
    have content := mixedPages_coalesce_parts d peers nodes (mixedInitialRows d peers) ctx ready freshAip
    rw [eq] at content ⊢
    rw [coalesce_mixedPageMessages_source d page tail nonempty header,content]
    rfl

end Leanux.Proofs.WG.Config
