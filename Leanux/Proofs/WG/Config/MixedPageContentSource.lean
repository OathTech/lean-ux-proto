import Leanux.Proofs.WG.Config.MixedPageContentModel
import Leanux.Proofs.WG.Config.MixedPageScanInput
import Leanux.Proofs.WG.Config.MixedPageScanClaims
import Leanux.Proofs.WG.Config.MixedPeerCoalesceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual fixed fields never contain an allowed-IP array, including malformed
endpoint families. -/
theorem mixedPeerFixed_canonical (p : Peer) (ctx : DumpCtx) :
    ∀ item ∈ mixedPeerFixed p ctx, item.1 ≠ "allowed_ips" := by
  intro item member
  unfold mixedPeerFixed at member
  split at member
  · cases endpoint : p.endpoint <;> simp [peerFixedAttrs,endpoint] at member <;>
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [List.mem_singleton] at member
    subst item
    simp

/-- A completed serializer emits every supplied node in order. Missing nests
are normalized by the actual coalescer, not inserted into the serializer. -/
theorem weightedPeerResult_complete_parts (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (out : NlSkb) (after : DumpCtx) (attrs : PeerDumpAttrs)
    (result : weightedPeerResult d nodes p ctx skb ids = (out,after,.complete attrs)) :
    peerDumpWithIps attrs = coalesceAipPart (hexKey p.remoteStatic)
      (mixedPeerFixed p ctx) (dumpNodeJsons nodes ids) false := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  have canonical := mixedPeerFixed_canonical p ctx
  by_cases fitsPrefix : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,
      ite_eq_left fitsPrefix] at result
    cases ids with
    | nil =>
      simp only [weightedAllowedResult,Prod.mk.injEq,PeerDump.complete.injEq] at result
      have attrsEq := result.2.2
      subst attrs
      have noIps : (mixedPeerFixed p ctx).any (·.1 == "allowed_ips") = false := by
        apply List.any_eq_false.mpr
        intro item member
        simpa only [beq_iff_eq] using canonical item member
      change peerDumpWithIps {publicKey := hexKey p.remoteStatic, attrs := mixedPeerFixed p ctx} = _
      simp only [peerDumpWithIps,noIps,Bool.false_eq_true,ite_false]
      rfl
    | cons id ids =>
      by_cases nest : skb.room-cost < 4
      · simp [weightedAllowedResult,nest] at result
      · simp only [weightedAllowedResult,ite_eq_right nest] at result
        cases plan : weightedPrefix nodes (skb.room-cost-4) (id::ids) with
        | mk front remaining =>
          rw [plan] at result
          cases remaining with
          | nil =>
            have decomp := (weightedPrefix_spec nodes (skb.room-cost-4) (id::ids)).1
            rw [plan] at decomp
            simp only [List.append_nil] at decomp
            subst front
            simp only [Prod.mk.injEq,PeerDump.complete.injEq] at result
            have attrsEq := result.2.2
            subst attrs
            simp [peerDumpWithIps,coalesceAipPart,mixedPeerFixed]
          | cons next rest => simp at result
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,ite_eq_right fitsPrefix] at result
    simp at result

/-- A split emits an exact prefix and retains its nonempty complement. This
includes zero-node first fragments and arbitrary stored node widths. -/
theorem weightedPeerResult_split_parts (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (out : NlSkb) (after : DumpCtx) (attrs : PeerDumpAttrs)
    (result : weightedPeerResult d nodes p ctx skb ids = (out,after,.split attrs)) :
    ∃ front start rest, ids = front ++ start::rest ∧
      mixedPeerRemaining nodes p ctx skb ids = start::rest ∧
      after.nextAllowedip = some start ∧
      attrs = coalesceAipPart (hexKey p.remoteStatic)
        (mixedPeerFixed p ctx) (dumpNodeJsons nodes front) true := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fitsPrefix : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,
      ite_eq_left fitsPrefix] at result
    cases ids with
    | nil => simp [weightedAllowedResult] at result
    | cons id ids =>
      by_cases nest : skb.room-cost < 4
      · simp [weightedAllowedResult,nest] at result
      · simp only [weightedAllowedResult,ite_eq_right nest] at result
        cases plan : weightedPrefix nodes (skb.room-cost-4) (id::ids) with
        | mk front remaining =>
          rw [plan] at result
          cases remaining with
          | nil => simp at result
          | cons start rest =>
            have decomp := (weightedPrefix_spec nodes (skb.room-cost-4) (id::ids)).1
            rw [plan] at decomp
            simp only [Prod.mk.injEq,PeerDump.split.injEq] at result
            refine ⟨front,start,rest,decomp.symm,?_,?_,?_⟩
            · simp only [mixedPeerRemaining,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,plan]
            · exact congrArg DumpCtx.nextAllowedip result.2.1.symm
            · exact result.2.2.symm
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,ite_eq_right fitsPrefix] at result
    simp at result

/-- Exact scan content: completing its retained suffix with the actual inner
coalescer recovers every original row and node occurrence. This does not assert
that a real callback can serialize the virtual suffix in one page. -/
theorem mixedPeerScan_complete_parts (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (safe : prior.map peerDumpWithIps = #[] ∨ (prior.map peerDumpWithIps).back!.split = false) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    forIn (mixedRowsParts peers nodes result.native.1 result.remaining)
      (result.native.2.2.2.2.map peerDumpWithIps,true) coalescePeerStep =
      (pure (prior.map peerDumpWithIps ++ (mixedRowsParts peers nodes ctx rows).toArray,
        result.remaining.isEmpty) : WG.M _) := by
  have normalized (key : String) (fixed : List (String × Json)) (ips : Array Json) (flag : Bool) :
      peerDumpWithIps (coalesceAipPart key fixed ips flag) = coalesceAipPart key fixed ips flag := by
    simp [peerDumpWithIps,coalesceAipPart]
  have rowsNormalized (rows : List MixedPeerRow) (ctx : DumpCtx) :
      (mixedRowsParts peers nodes ctx rows).map peerDumpWithIps = mixedRowsParts peers nodes ctx rows := by
    cases rows with
    | nil => rfl
    | cons row rows => simp [mixedRowsParts,normalized,List.map_map,Function.comp_def]
  induction rows generalizing ctx cursor skb prior with
  | nil => simp [mixedPeerScan,mixedRowsParts]
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      cases verdict with
      | complete attrs =>
        have content := weightedPeerResult_complete_parts d nodes (peers pid) ctx skb ids out after attrs outcome
        have reset := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs
          (by rw [outcome])
        simp only [outcome] at reset
        have nextSafe : (prior.push attrs).map peerDumpWithIps = #[] ∨
            ((prior.push attrs).map peerDumpWithIps).back!.split = false := by
          right
          simp [content,coalesceAipPart]
        have later := ih after (some pid) out (prior.push attrs) nextSafe
        simp only [mixedPeerScan,outcome]
        rw [later]
        have suffix : mixedRowsParts peers nodes after rows = rows.map
            (fun row => coalesceAipPart (hexKey (peers row.1).remoteStatic)
              (peerFixedAttrs (peers row.1)) (dumpNodeJsons nodes row.2) false) := by
          cases rows with
          | nil => rfl
          | cons row rows => simp [mixedRowsParts,mixedPeerFixed,reset]
        rw [suffix]
        simp [Array.map_push,content,mixedRowsParts]
      | split attrs =>
        obtain ⟨front,start,tail,decomp,remaining,next,content⟩ :=
          weightedPeerResult_split_parts d nodes (peers pid) ctx skb ids out after attrs outcome
        simp only [mixedPeerScan,outcome,remaining]
        have fixed : mixedPeerFixed (peers pid) after = [("public_key",toJson (hexKey (peers pid).remoteStatic))] := by
          simp [mixedPeerFixed,next]
        simp only [mixedRowsParts,fixed,Array.map_push,content,normalized]
        rw [coalescePeers_continuation_front _ _ _ _ _ _ _ (mixedPeerFixed_canonical (peers pid) ctx)]
        have arrays : dumpNodeJsons nodes front ++ dumpNodeJsons nodes (start::tail) = dumpNodeJsons nodes ids := by
          rw [decomp]
          simp [dumpNodeJsons]
        simp [arrays,normalized,List.map_map,Function.comp_def]
      | cancelled =>
        have phase := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
        simp only [outcome] at phase
        have parts : mixedRowsParts peers nodes after ((pid,ids)::rows) =
            mixedRowsParts peers nodes ctx ((pid,ids)::rows) := by
          simp only [mixedRowsParts,mixedPeerFixed,phase.1]
        simp only [mixedPeerScan,outcome,parts]
        rw [coalescePeers_complete_front _ _ safe,rowsNormalized]
        rfl

end Leanux.Proofs.WG.Config
