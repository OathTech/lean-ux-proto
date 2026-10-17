import Leanux.Proofs.WG.Config.MixedCoalesceScanSource
import Leanux.Proofs.WG.Config.MixedPagePlanClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual inner loop for one page, with only its reset first-item flag. -/
def mixedCoalescePage (page : MixedPeerScan) (acc : Array PeerDumpAttrs) :
    WG.M (ForInStep (Array PeerDumpAttrs)) := do
  let out ← forIn page.native.2.2.2.2.toList (acc,true) coalescePeerStep
  return .yield out.1

/-- Every real canonical page preserves and finally completes the content
invariant. Boundary freshness is unnecessary for this pure serializer theorem;
the native producer proves first-match selection separately. -/
theorem mixedPages_coalesce_context (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (acc target : Array PeerDumpAttrs) (context : MixedCoalesceState peers nodes rows ctx acc target) :
    forIn (mixedPages d peers nodes rows ctx ready) acc mixedCoalescePage = (pure target : WG.M _) := by
  let page := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  obtain ⟨next,flag,pageRun,nextContext⟩ := mixedPage_coalesce_context d peers nodes rows ctx
    {room := mixedPageRoom d ctx} acc target context
  change forIn page.native.2.2.2.2.toList (acc,true) coalescePeerStep = (pure (next,flag) : WG.M _) at pageRun
  change MixedCoalesceState peers nodes page.remaining page.native.1 next target at nextContext
  dsimp only [page] at pageRun
  rw [mixedPages]
  dsimp only
  by_cases finished : page.remaining = []
  · rw [dite_eq_left finished]
    have final : next = target := by
      rw [finished] at nextContext
      cases phase : page.native.1.nextAllowedip with
      | none =>
        simp only [MixedCoalesceState,phase,mixedRowsParts,Array.append_empty] at nextContext
        exact nextContext.2.symm
      | some id =>
        simp only [MixedCoalesceState,phase] at nextContext
        obtain ⟨pid,ids,rest,before,fixed,done,eq,_⟩ := nextContext
        cases eq
    simp only [List.forIn_cons,List.forIn_nil,mixedCoalescePage,pageRun,pure_bind,final]
  · rw [dite_eq_right finished]
    have nextReady := mixedPageReady_next d peers nodes rows ctx ready finished
    have state : MixedCoalesceState peers nodes page.remaining
        {page.native.1 with nextPeer := page.native.2.1} next target := by
      simpa only [MixedCoalesceState,mixedRowsParts,mixedPeerFixed] using nextContext
    have later := mixedPages_coalesce_context d peers nodes page.remaining
      {page.native.1 with nextPeer := page.native.2.1} nextReady next target state
    simp only [List.forIn_cons,mixedCoalescePage,pageRun,pure_bind]
    exact later
termination_by mixedPageMeasure rows ctx
decreasing_by exact mixedPageReady_progress d peers nodes rows ctx ready finished

/-- Fresh canonical occurrence rows coalesce exactly, including duplicates,
arbitrary endpoint fields and arbitrary stored node widths. This is the inner
peer fold; the DATA headers and DONE envelope are connected separately. -/
theorem mixedPages_coalesce_parts (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (fresh : ctx.nextAllowedip = none) :
    forIn (mixedPages d peers nodes rows ctx ready) #[] mixedCoalescePage =
      (pure (mixedRowsParts peers nodes ctx rows).toArray : WG.M _) := by
  apply mixedPages_coalesce_context
  simp [MixedCoalesceState,fresh]

end Leanux.Proofs.WG.Config
