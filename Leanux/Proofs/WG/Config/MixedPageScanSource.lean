import Leanux.Proofs.WG.Config.MixedPageScanInput
import Leanux.Proofs.WG.Config.MixedPeerSerializerSource
import Leanux.Proofs.WG.Config.MultiPeerDumpSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual finite peer loop produces the literal mixed scan, including
zero-node splits, cancellation and every branch event. The first suffix and
later full lists are tied to resident/readable source data, with a current
sequence. No page-fit, global uniqueness or successful-loop premise is used. -/
theorem mixedPeerScan_native (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (residents : ∀ row ∈ rows, d.peers[row.1]? = some (peers row.1))
    (readable : ∀ row ∈ rows, ∀ id ∈ row.2, d.nodes[id]? = some (nodes id))
    (selected : MixedRowsSelected peers rows ctx)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    Returns (forIn (rows.map Prod.fst) (ctx,cursor,skb,true,prior) deviceDumpPeersStep)
      (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧
        result = (mixedPeerScan d peers nodes rows ctx cursor skb prior).native) := by
  induction rows generalizing ctx cursor skb prior with
  | nil =>
    intro g ambient device
    exact ⟨_,g,ambient,rfl,device,rfl⟩
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one : Returns (getPeerDump pid ctx skb) (fun g => g.dev = some d)
        (fun result g => g.dev = some d ∧ result = weightedPeerResult d nodes (peers pid) ctx skb ids) := by
      cases hcursor : ctx.nextAllowedip with
      | none =>
        have initial : (peers pid).allowedipsList = ids := by
          simpa only [MixedRowsSelected,hcursor] using selected.1
        exact getPeerDump_weighted_fresh_room pid d nodes (peers pid) ctx skb ids
          (residents (pid,ids) (by simp)) hcursor initial
          (readable (pid,ids) (by simp)) sequence
      | some start =>
        have initial : ids.head? = some start ∧
            (peers pid).allowedipsList.dropWhile (· != start) = ids := by
          simpa only [MixedRowsSelected,hcursor] using selected.1
        exact getPeerDump_weighted_resume_room pid d nodes (peers pid) ctx skb start ids
          (residents (pid,ids) (by simp)) hcursor initial.1 initial.2
          (readable (pid,ids) (by simp)) sequence
    intro g ambient device
    let mark (a : Ambient) (site : Decision) (value : Bool) : Ambient :=
      {a with steps := a.steps.push {decision := site,outcome := value,netRx := a.netRxSection}}
    let before := mark ambient .dumpPeerIter true
    obtain ⟨value,middle,inputs,run,midDevice,valueEq⟩ := one g before device
    subst value
    cases resultEq : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk outSkb out =>
      obtain ⟨outCtx,part⟩ := out
      cases part with
      | complete attrs =>
        have reset : outCtx = {ctx with nextAllowedip := none,allowedipsSeq := 0} := by
          have fact := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs
            (by rw [resultEq])
          simpa only [resultEq] using fact
        have nextSelected : MixedRowsSelected peers rows outCtx := by
          cases rows with
          | nil => trivial
          | cons next rest =>
            constructor
            · simpa only [reset] using selected.2 next (by simp)
            · intro row member
              exact selected.2 row (by simp [member])
        let nextInputs := mark inputs .dumpGetPeerFail false
        obtain ⟨result,final,after,tailRun,finalDevice,finalValue⟩ :=
          ih outCtx (some pid) outSkb (prior.push attrs)
            (fun row member => residents row (by simp [member]))
            (fun row member => readable row (by simp [member]))
            nextSelected (by simp [reset])
            middle nextInputs midDevice
        refine ⟨result,final,after,?_,finalDevice,?_⟩
        · rw [List.map_cons,List.forIn_cons]
          simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
          change (((getPeerDump pid ctx skb).run g).run before >>= _) = _
          rw [run,resultEq]
          change ((forIn rows (outCtx,some pid,outSkb,true,prior.push attrs)
            (fun row state => deviceDumpPeersStep row.1 state)).run middle).run nextInputs = _
          simpa only [List.forIn_map] using tailRun
        · simpa only [mixedPeerScan,resultEq] using finalValue
      | split attrs =>
        refine ⟨_,middle,mark inputs .dumpGetPeerFail true,?_,midDevice,rfl⟩
        rw [List.map_cons,List.forIn_cons]
        simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
        change (((getPeerDump pid ctx skb).run g).run before >>= _) = _
        rw [run,resultEq]
        simp [mixedPeerScan,resultEq,mark]
        rfl
      | cancelled =>
        refine ⟨_,middle,mark inputs .dumpGetPeerFail true,?_,midDevice,rfl⟩
        rw [List.map_cons,List.forIn_cons]
        simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
        change (((getPeerDump pid ctx skb).run g).run before >>= _) = _
        rw [run,resultEq]
        simp [mixedPeerScan,resultEq,mark]
        rfl

end Leanux.Proofs.WG.Config
