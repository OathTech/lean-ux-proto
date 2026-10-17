import Leanux.Proofs.WG.Config.MixedCoalesceStepSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The actual inner step has no break branch; errors remain exact while
peer lists concatenate through the actual forIn. -/
theorem coalescePeers_append (front tail : List PeerDumpAttrs) (state : Array PeerDumpAttrs × Bool) :
    forIn (front ++ tail) state coalescePeerStep =
      (forIn front state coalescePeerStep >>= fun out => forIn tail out coalescePeerStep : WG.M _) := by
  induction front generalizing state with
  | nil => simp
  | cons attrs front ih =>
    simp only [List.cons_append,List.forIn_cons,bind_assoc]
    simp only [coalescePeerStep]
    split
    · split
      · rfl
      · split
        · simp only [pure_bind,ih]
        · rfl
    · simp only [pure_bind,ih]

/-- The scan extends an actual inner-loop prefix. Its final accumulator has
the same fixed target; no source callback or successful-page premise is used. -/
theorem mixedPeerScan_coalesce_context (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId) (skb : NlSkb)
    (prior : Array PeerDumpAttrs) (entry acc target : Array PeerDumpAttrs) (entryFirst first : Bool)
    (prefixRun : forIn prior.toList (entry,entryFirst) coalescePeerStep = (pure (acc,first) : WG.M _))
    (context : MixedCoalesceState peers nodes rows ctx acc target)
    (initial : ctx.nextAllowedip ≠ none → first = true) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    ∃ next flag, forIn result.native.2.2.2.2.toList (entry,entryFirst) coalescePeerStep =
        (pure (next,flag) : WG.M _) ∧
      MixedCoalesceState peers nodes result.remaining result.native.1 next target := by
  induction rows generalizing ctx cursor skb prior acc first with
  | nil => exact ⟨acc,first,prefixRun,context⟩
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      cases verdict with
      | complete attrs =>
        obtain ⟨next,step,nextContext⟩ := mixedCoalesce_complete d peers nodes pid ids rows ctx skb
          out after attrs acc target first context initial outcome
        have nextRun : forIn (prior.push attrs).toList (entry,entryFirst) coalescePeerStep =
            (pure (next,false) : WG.M _) := by
          simp only [Array.toList_push,coalescePeers_append,List.forIn_cons,List.forIn_nil,prefixRun,pure_bind,step]
        have reset := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs
          (by rw [outcome])
        simp only [outcome] at reset
        have later := ih after (some pid) out (prior.push attrs) next false nextRun nextContext
          (by simp [reset])
        simpa only [mixedPeerScan,outcome] using later
      | split attrs =>
        obtain ⟨next,step,nextContext⟩ := mixedCoalesce_split d peers nodes pid ids rows ctx skb
          out after attrs acc target first context initial outcome
        simp only [mixedPeerScan,outcome]
        refine ⟨next,false,?_,nextContext⟩
        simp only [Array.toList_push,coalescePeers_append,List.forIn_cons,List.forIn_nil,prefixRun,pure_bind,step]
      | cancelled =>
        have phase := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
        simp only [outcome] at phase
        simp only [mixedPeerScan,outcome]
        refine ⟨acc,first,prefixRun,?_⟩
        simpa only [MixedCoalesceState,phase.1,mixedRowsParts,mixedPeerFixed] using context

/-- A complete canonical page preserves the content invariant by executing
its actual emitted peer records. The accumulator is supplied as data, not as
an assumed successful coalescer result. -/
theorem mixedPage_coalesce_context (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (skb : NlSkb) (acc target : Array PeerDumpAttrs)
    (context : MixedCoalesceState peers nodes rows ctx acc target) :
    let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer skb #[]
    ∃ next flag, forIn result.native.2.2.2.2.toList (acc,true) coalescePeerStep =
        (pure (next,flag) : WG.M _) ∧
      MixedCoalesceState peers nodes result.remaining result.native.1 next target := by
  exact mixedPeerScan_coalesce_context d peers nodes rows ctx ctx.nextPeer skb #[] acc acc target true true
    (by simp) context (fun _ => rfl)

end Leanux.Proofs.WG.Config
