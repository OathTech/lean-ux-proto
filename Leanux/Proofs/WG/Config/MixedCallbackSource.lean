import Leanux.Proofs.WG.Config.MixedCallbackFrames
import Leanux.Proofs.WG.Config.MixedPageScanSource
import Leanux.Proofs.WG.Config.CursorReadySource
import Leanux.Proofs.WG.Config.PeerPageStartSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Compose the exact native mixed loop with the original end marker and
acquire-before-release finalizer. Reference bounds concern the actual current
and post-acquisition Devices; no successful-loop premise is supplied. -/
theorem mixedPeerLoopFinish_returns (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (flags : Nat)
    (attrs : List (String × Json)) (skb : NlSkb)
    (residents : ∀ row ∈ rows, d.peers[row.1]? = some (peers row.1))
    (readable : ∀ row ∈ rows, ∀ id ∈ row.2, d.nodes[id]? = some (nodes id))
    (selected : MixedRowsSelected peers rows ctx)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    let state := (mixedPeerScan d peers nodes rows ctx ctx.nextPeer skb #[]).native
    (∀ id, (if state.2.2.2.1 then none else state.2.1) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31) →
    (∀ id, ctx.nextPeer = some id →
      ∃ p, (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)).peers[id]? = some p ∧
        1 < p.refcount) →
    Returns (cursorLoopFinish d (rows.map Prod.fst) ctx flags attrs skb)
      (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs state.1 state.2.1 state.2.2.1
          state.2.2.2.1 (some state.2.2.2.2) ∧
        g.dev = some (cursorHandoff d ctx.nextPeer (if state.2.2.2.1 then none else state.2.1))) := by
  dsimp only
  intro acquireReady releaseReady g ambient device
  obtain ⟨value,middle,remaining,loopRun,same,valueEq⟩ :=
    mixedPeerScan_native d peers nodes rows ctx ctx.nextPeer skb #[]
      residents readable selected sequence g ambient device
  subst value
  have old := mixedPeerScan_oldCursor d peers nodes rows ctx ctx.nextPeer skb #[]
  generalize stateEq : (mixedPeerScan d peers nodes rows ctx ctx.nextPeer skb #[]).native = state
    at loopRun old acquireReady releaseReady ⊢
  obtain ⟨outCtx,cursor,outSkb,done,parts⟩ := state
  change outCtx.nextPeer = ctx.nextPeer at old
  have finish := cursorFinish_ready_returns d flags attrs outCtx cursor outSkb done (some parts)
    acquireReady (by simpa only [old] using releaseReady)
  cases done with
  | false =>
    obtain ⟨result,final,after,run,post⟩ := finish middle remaining same
    refine ⟨result,final,after,?_,?_⟩
    · simp only [cursorLoopFinish]
      change (((forIn (rows.map Prod.fst) (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep).run g).run ambient >>= _) = _
      rw [loopRun]
      exact run
    · simpa only [old] using post
  | true =>
    let inputs : Ambient := {remaining with steps := remaining.steps.push {
      decision := .dumpPeerIter,outcome := false,netRx := remaining.netRxSection}}
    obtain ⟨result,final,after,run,post⟩ := finish middle inputs same
    refine ⟨result,final,after,?_,?_⟩
    · simp only [cursorLoopFinish]
      change (((forIn (rows.map Prod.fst) (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep).run g).run ambient >>= _) = _
      rw [loopRun]
      exact run
    · simpa only [old] using post

/-- Whole original fresh-buffer callback through its false guard. First-peer
AIP continuations still have no peer cursor and repeat the device header;
held-cursor callbacks omit it. All split/cancel outcomes remain in the scan. -/
theorem wgGetDeviceDump_mixed_returns (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (prev : Nat)
    (residents : ∀ row ∈ rows, d.peers[row.1]? = some (peers row.1))
    (readable : ∀ row ∈ rows, ∀ id ∈ row.2, d.nodes[id]? = some (nodes id))
    (selected : MixedRowsSelected peers rows ctx)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (rowIds : rows.map Prod.fst = cursorSelected d ctx)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p)
    (continues : cursorGuardValue d ctx = false)
    (headerFits : ctx.nextPeer.isNone = true → devicePrefixSpace d ≤ NLMSG_GOODSIZE) :
    let header := cursorHeaderSkb d ctx {}
    let state := (mixedPeerScan d peers nodes rows ctx ctx.nextPeer {header with room := header.room-4} #[]).native
    (∀ id, (if state.2.2.2.1 then none else state.2.1) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31) →
    (∀ id, ctx.nextPeer = some id →
      ∃ p, (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)).peers[id]? = some p ∧
        1 < p.refcount) →
    Returns (wgGetDeviceDump ctx prev {}) (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d
          (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
          (if ctx.nextPeer.isNone then deviceFixedAttrs d else [])
          state.1 state.2.1 state.2.2.1 state.2.2.2.1 (some state.2.2.2.2) ∧
        g.dev = some (cursorHandoff d ctx.nextPeer (if state.2.2.2.1 then none else state.2.1))) := by
  dsimp only
  intro acquireReady releaseReady
  let header := cursorHeaderSkb d ctx {}
  have nest : 4 ≤ header.room := by
    cases old : ctx.nextPeer with
    | none =>
      have fits := headerFits (by simp [old])
      have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
      have same : header = cursorHeaderSkb d {hasWg := true} {} := by
        simp only [header,cursorHeaderSkb,old,Option.isNone_none,ite_true]
      rw [same,peerFirstHeader_exact d fits]
      dsimp
      omega
    | some pid => simp [header,cursorHeaderSkb,old,NlSkb.put,nlmsgTotal]
  let flags := 2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0
  let attrs := if ctx.nextPeer.isNone then deviceFixedAttrs d else []
  let state := (mixedPeerScan d peers nodes rows ctx ctx.nextPeer {header with room := header.room-4} #[]).native
  let R : DumpCall → WGWorld → Prop := fun result g =>
    result = cursorCallResult d flags attrs state.1 state.2.1 state.2.2.1 state.2.2.2.1
      (some state.2.2.2.2) ∧
    g.dev = some (cursorHandoff d ctx.nextPeer (if state.2.2.2.1 then none else state.2.1))
  have loop : Returns (cursorLoopFinish d (cursorSelected d ctx) ctx flags attrs
      {header with room := header.room-4}) (fun g => g.dev = some d) R := by
    rw [←rowIds]
    exact mixedPeerLoopFinish_returns d peers nodes rows ctx flags attrs _
      residents readable selected sequence acquireReady releaseReady
  have body : Returns (cursorDumpBody d ctx flags attrs header) (fun g => g.dev = some d) R :=
    TwoPage.cursorBody_loop_returns d ctx flags attrs header R nest oldResident continues loop
  have call := TwoPage.cursorHeader_fresh_returns d ctx prev headerFits
    (cursorDumpBody d ctx) (fun g => g.dev = some d) R body
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

/-- The actual empty-list/dead-cursor guard cancels the peer nest and releases
its held cursor. It needs no serializer or row assumptions and preserves the
original header flags, repeated device attributes and post-nest room. -/
theorem wgGetDeviceDump_guard_returns (d : Device) (ctx : DumpCtx) (prev : Nat)
    (skip : cursorGuardValue d ctx = true)
    (headerFits : ctx.nextPeer.isNone = true → devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (releaseReady : ∀ id, ctx.nextPeer = some id →
      ∃ p, d.peers[id]? = some p ∧ 1 < p.refcount) :
    let header := cursorHeaderSkb d ctx {}
    Returns (wgGetDeviceDump ctx prev {}) (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d
          (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
          (if ctx.nextPeer.isNone then deviceFixedAttrs d else []) ctx ctx.nextPeer
          {header with room := header.room-4} true none ∧
        g.dev = some (cursorHandoff d ctx.nextPeer none)) := by
  dsimp only
  let header := cursorHeaderSkb d ctx {}
  have nest : 4 ≤ header.room := by
    cases old : ctx.nextPeer with
    | none =>
      have fits := headerFits (by simp [old])
      have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
      have same : header = cursorHeaderSkb d {hasWg := true} {} := by
        simp only [header,cursorHeaderSkb,old,Option.isNone_none,ite_true]
      rw [same,peerFirstHeader_exact d fits]
      dsimp
      omega
    | some pid => simp [header,cursorHeaderSkb,old,NlSkb.put,nlmsgTotal]
  let flags := 2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0
  let attrs := if ctx.nextPeer.isNone then deviceFixedAttrs d else []
  let R : DumpCall → WGWorld → Prop := fun result g =>
    result = cursorCallResult d flags attrs ctx ctx.nextPeer
      {header with room := header.room-4} true none ∧
    g.dev = some (cursorHandoff d ctx.nextPeer none)
  have finish : Returns (cursorDumpFinish d flags attrs ctx ctx.nextPeer
      {header with room := header.room-4} true none) (fun g => g.dev = some d) R :=
    cursorFinish_ready_returns d flags attrs ctx ctx.nextPeer _ true none
      (by intro id impossible; cases impossible)
      (by simpa only [ite_true,cursorAcquired] using releaseReady)
  have body : Returns (cursorDumpBody d ctx flags attrs header) (fun g => g.dev = some d) R := by
    intro g ambient device
    have enough : ¬header.room < 4 := by omega
    let before : Ambient := {ambient with steps := ambient.steps.push {
      decision := .dumpNoPeersNest,outcome := false,netRx := ambient.netRxSection}}
    obtain ⟨value,middle,inputs,guardRun,valueEq,same⟩ := cursorDumpGuard_returns d ctx
      (fun id old => let ⟨p,resident,_⟩ := releaseReady id old; ⟨p,resident⟩) g before device
    have isTrue : value = true := valueEq.trans skip
    subst value
    obtain ⟨result,final,after,run,post⟩ := finish middle inputs same
    refine ⟨result,final,after,?_,post⟩
    simp [cursorDumpBody,NlSkb.put,nlaTotal,enough,branch,AmbientM.branch]
    change (((cursorDumpGuard d ctx).run g).run before >>= _) = _
    rw [guardRun,skip]
    exact run
  have call := TwoPage.cursorHeader_fresh_returns d ctx prev headerFits
    (cursorDumpBody d ctx) (fun g => g.dev = some d) R body
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

end Leanux.Proofs.WG.Config
