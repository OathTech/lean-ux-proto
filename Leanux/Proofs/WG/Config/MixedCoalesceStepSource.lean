import Leanux.Proofs.WG.Config.MixedCoalesceContextModel
import Leanux.Proofs.WG.Config.MixedPageContentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- A complete previous record disables continuation, even for repeated keys. -/
theorem coalescePeerStep_fresh (attrs : PeerDumpAttrs) (acc : Array PeerDumpAttrs) (first : Bool)
    (safe : acc = #[] ∨ acc.back!.split = false) :
    coalescePeerStep attrs (acc,first) = (pure (.yield (acc.push (peerDumpWithIps attrs),false)) : WG.M _) := by
  have noContinue : (first && acc.size > 0 && acc.back!.split && acc.back!.publicKey == attrs.publicKey) = false := by
    rcases safe with rfl | last
    · simp
    · simp [last]
  simp only [coalescePeerStep,noContinue,Bool.false_eq_true,ite_false]

/-- A nonempty completed suffix retains its actual allowed-IP nest. -/
theorem weightedPeerResult_complete_nonempty (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (out : NlSkb) (after : DumpCtx) (attrs : PeerDumpAttrs)
    (nonempty : ids ≠ [])
    (result : weightedPeerResult d nodes p ctx skb ids = (out,after,.complete attrs)) :
    attrs = coalesceAipPart (hexKey p.remoteStatic) (mixedPeerFixed p ctx) (dumpNodeJsons nodes ids) false := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fits : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,
      ite_eq_left fits] at result
    cases ids with
    | nil => exact False.elim (nonempty rfl)
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
            exact result.2.2.symm
          | cons next rest => simp at result
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40)=cost from rfl,
      ite_eq_right fits] at result
    simp at result

/-- Completing the actual current occurrence moves it into the full prefix. -/
theorem mixedCoalesce_complete (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (pid : PeerId) (ids : List NodeId) (rows : List MixedPeerRow) (ctx : DumpCtx) (skb : NlSkb)
    (out : NlSkb) (after : DumpCtx) (attrs : PeerDumpAttrs) (acc target : Array PeerDumpAttrs)
    (first : Bool) (context : MixedCoalesceState peers nodes ((pid,ids)::rows) ctx acc target)
    (initial : ctx.nextAllowedip ≠ none → first = true)
    (result : weightedPeerResult d nodes (peers pid) ctx skb ids = (out,after,.complete attrs)) :
    ∃ next, coalescePeerStep attrs (acc,first) = (pure (.yield (next,false)) : WG.M _) ∧
      MixedCoalesceState peers nodes rows after next target := by
  have reset := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs (by rw [result])
  simp only [result] at reset
  cases phase : ctx.nextAllowedip with
  | none =>
    have current := context
    simp only [MixedCoalesceState,phase] at current
    refine ⟨acc.push (peerDumpWithIps attrs),coalescePeerStep_fresh attrs acc first current.1,?_⟩
    have content := weightedPeerResult_complete_parts d nodes (peers pid) ctx skb ids out after attrs result
    rw [reset]
    simp only [MixedCoalesceState]
    constructor
    · right
      simp [content,coalesceAipPart]
    · rw [current.2,content]
      cases rows <;> simp [mixedRowsParts,mixedPeerFixed,phase]
  | some start =>
    have firstTrue := initial (by simp [phase])
    subst first
    simp only [MixedCoalesceState,phase] at context
    obtain ⟨pid',ids',rest,before,fixed,done,eq,nonempty,canonical,accEq,targetEq⟩ := context
    cases eq
    have content := weightedPeerResult_complete_nonempty d nodes (peers pid) ctx skb ids out after attrs nonempty result
    have fixedEq : mixedPeerFixed (peers pid) ctx = [("public_key",toJson (hexKey (peers pid).remoteStatic))] := by
      simp [mixedPeerFixed,phase]
    refine ⟨done.push (coalesceAipPart (hexKey (peers pid).remoteStatic) fixed
      (before ++ dumpNodeJsons nodes ids) false),?_,?_⟩
    · rw [accEq,content,fixedEq]
      exact coalescePeerStep_continuation done _ fixed before _ false canonical
    · rw [reset]
      simp only [MixedCoalesceState]
      refine ⟨Or.inr (by simp [coalesceAipPart]),?_⟩
      exact targetEq

/-- An actual split extends the canonical partial record with exactly its
emitted node prefix; the following continuation remains nonempty. -/
theorem mixedCoalesce_split (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (pid : PeerId) (ids : List NodeId) (rows : List MixedPeerRow) (ctx : DumpCtx) (skb : NlSkb)
    (out : NlSkb) (after : DumpCtx) (attrs : PeerDumpAttrs) (acc target : Array PeerDumpAttrs)
    (first : Bool) (context : MixedCoalesceState peers nodes ((pid,ids)::rows) ctx acc target)
    (initial : ctx.nextAllowedip ≠ none → first = true)
    (result : weightedPeerResult d nodes (peers pid) ctx skb ids = (out,after,.split attrs)) :
    ∃ next, coalescePeerStep attrs (acc,first) = (pure (.yield (next,false)) : WG.M _) ∧
      MixedCoalesceState peers nodes ((pid,mixedPeerRemaining nodes (peers pid) ctx skb ids)::rows) after next target := by
  obtain ⟨front,start,tail,decomp,remaining,newPhase,content⟩ :=
    weightedPeerResult_split_parts d nodes (peers pid) ctx skb ids out after attrs result
  have arrays : dumpNodeJsons nodes front ++ dumpNodeJsons nodes (start::tail) = dumpNodeJsons nodes ids := by
    rw [decomp]
    simp [dumpNodeJsons]
  have sameTail : mixedRowsParts peers nodes {after with nextAllowedip := none} rows =
      mixedRowsParts peers nodes {ctx with nextAllowedip := none} rows := by
    cases rows <;> rfl
  cases phase : ctx.nextAllowedip with
  | none =>
    have current := context
    simp only [MixedCoalesceState,phase] at current
    refine ⟨acc.push (peerDumpWithIps attrs),coalescePeerStep_fresh attrs acc first current.1,?_⟩
    simp only [MixedCoalesceState,newPhase,remaining]
    refine ⟨pid,start::tail,rows,dumpNodeJsons nodes front,mixedPeerFixed (peers pid) ctx,acc,
      rfl,by simp,mixedPeerFixed_canonical (peers pid) ctx,?_,?_⟩
    · simp [content,peerDumpWithIps,coalesceAipPart]
    · rw [sameTail,arrays,current.2]
      cases rows <;> simp [mixedRowsParts,mixedPeerFixed,phase]
  | some old =>
    have firstTrue := initial (by simp [phase])
    subst first
    simp only [MixedCoalesceState,phase] at context
    obtain ⟨pid',ids',rest,before,fixed,done,eq,nonempty,canonical,accEq,targetEq⟩ := context
    cases eq
    have fixedEq : mixedPeerFixed (peers pid) ctx = [("public_key",toJson (hexKey (peers pid).remoteStatic))] := by
      simp [mixedPeerFixed,phase]
    refine ⟨done.push (coalesceAipPart (hexKey (peers pid).remoteStatic) fixed
      (before ++ dumpNodeJsons nodes front) true),?_,?_⟩
    · rw [accEq,content,fixedEq]
      exact coalescePeerStep_continuation done _ fixed before _ true canonical
    · simp only [MixedCoalesceState,newPhase,remaining]
      refine ⟨pid,start::tail,rows,before ++ dumpNodeJsons nodes front,fixed,done,
        rfl,by simp,canonical,rfl,?_⟩
      rw [Array.append_assoc,arrays,sameTail]
      exact targetEq

end Leanux.Proofs.WG.Config
