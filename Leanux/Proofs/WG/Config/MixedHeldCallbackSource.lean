import Leanux.Proofs.WG.Config.MixedCallbackSource
import Leanux.Proofs.WG.Config.MixedPageReferenceFrames
import Leanux.Proofs.WG.Config.CursorStepEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The planned room is the exact original fresh-buffer header after its peer
nest reservation. -/
theorem mixedPageHeader_exact (d : Device) (ctx : DumpCtx)
    (headerFits : ctx.nextPeer.isNone = true → devicePrefixSpace d ≤ NLMSG_GOODSIZE) :
    {cursorHeaderSkb d ctx {} with room := (cursorHeaderSkb d ctx {}).room-4} =
      {room := mixedPageRoom d ctx} := by
  cases old : ctx.nextPeer with
  | none =>
    have fits := headerFits (by simp [old])
    have same : cursorHeaderSkb d ctx {} = cursorHeaderSkb d {hasWg := true} {} := by
      simp only [cursorHeaderSkb,old,Option.isNone_none,ite_true]
    rw [same,peerFirstHeader_exact d fits]
    simp only [mixedPageRoom,old,Option.isNone_none,ite_true]
    congr 1
    have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
    omega
  | some id => simp [cursorHeaderSkb,mixedPageRoom,old,NlSkb.put,nlmsgTotal,NLMSG_GOODSIZE]

/-- Static baseline data supplies the original mixed callback on its actual
held-reference Device, without a successful callback premise. -/
theorem mixedPage_held_returns (base current : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx) (prev : Nat)
    (held : CursorHeld base current ctx.nextPeer)
    (residents : ∀ row ∈ rows, base.peers[row.1]? = some (peers row.1))
    (readable : ∀ row ∈ rows, ∀ id ∈ row.2, base.nodes[id]? = some (nodes id))
    (selected : MixedRowsSelected peers rows ctx)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = base.peerAllowedips.seq)
    (rowIds : rows.map Prod.fst = cursorSelected base ctx)
    (continues : cursorGuardValue base ctx = false)
    (headerFits : ctx.nextPeer.isNone = true → devicePrefixSpace base ≤ NLMSG_GOODSIZE)
    (oldData : ∀ id, ctx.nextPeer = some id →
      ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount) :
    let scan := mixedPeerScan base peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom base ctx} #[]
    let next := if scan.native.2.2.2.1 then none else scan.native.2.1
    (∀ id, next = some id → ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount ∧
      p.refcount+1+(if ctx.nextPeer = some id then 1 else 0) < 2^31) →
    CursorHeld base (cursorHandoff current ctx.nextPeer next) next ∧
      Returns (wgGetDeviceDump ctx prev {}) (fun g => g.dev = some current)
        (fun result g => result = cursorCallResult base
            (2 + if prev != 0 && prev != base.deviceUpdateGen then 16 else 0)
            (if ctx.nextPeer.isNone then deviceFixedAttrs base else [])
            scan.native.1 scan.native.2.1 scan.native.2.2.1 scan.native.2.2.2.1
            (some scan.native.2.2.2.2) ∧
          g.dev = some (cursorHandoff current ctx.nextPeer next)) := by
  dsimp only
  intro newData
  let refs := fun id => (peers id).refcount + if ctx.nextPeer = some id then 1 else 0
  let values := fun id => {peers id with refcount := refs id}
  have fieldSeq : current.peerAllowedips.seq = base.peerAllowedips.seq :=
    congrArg (fun d => d.peerAllowedips.seq) held.1
  have fieldNodes : current.nodes = base.nodes := by
    have h := congrArg Device.nodes held.1
    exact h
  have fieldList : current.peerList = base.peerList := by
    have h := congrArg Device.peerList held.1
    exact h
  have space : devicePrefixSpace current = devicePrefixSpace base :=
    by
    have h := congrArg devicePrefixSpace held.1
    exact h
  have attrs : deviceFixedAttrs current = deviceFixedAttrs base :=
    by
    have h := congrArg deviceFixedAttrs held.1
    exact h
  have generation : current.deviceUpdateGen = base.deviceUpdateGen :=
    by
    have h := congrArg Device.deviceUpdateGen held.1
    exact h
  have currentResidents : ∀ row ∈ rows, current.peers[row.1]? = some (values row.1) := by
    intro row member
    have atRow := held.2 row.1
    rw [residents row member] at atRow
    dsimp only [Option.map_some] at atRow
    by_cases isOld : ctx.nextPeer = some row.1
    · simpa [values,refs,isOld] using atRow
    · simpa [values,refs,isOld] using atRow
  have currentReadable : ∀ row ∈ rows, ∀ id ∈ row.2, current.nodes[id]? = some (nodes id) := by
    simpa only [fieldNodes] using readable
  have currentSelected : MixedRowsSelected values rows ctx := by
    simpa only [MixedRowsSelected,values] using selected
  have currentSequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = current.peerAllowedips.seq := by
    simpa only [fieldSeq] using sequence
  have currentIds : rows.map Prod.fst = cursorSelected current ctx := by
    simpa only [cursorSelected,fieldList] using rowIds
  have currentOld : ∀ id, ctx.nextPeer = some id → ∃ p, current.peers[id]? = some p := by
    intro id old
    obtain ⟨p,found,_⟩ := oldData id old
    exact ⟨{p with refcount := p.refcount+1},by simpa [found,old] using held.2 id⟩
  have currentContinues : cursorGuardValue current ctx = false := by
    cases old : ctx.nextPeer with
    | none => simpa [cursorGuardValue,old,fieldList] using continues
    | some id =>
      obtain ⟨p,found,_⟩ := oldData id old
      have actual : current.peers[id]? = some {p with refcount := p.refcount+1} := by
        simpa [found,old] using held.2 id
      simpa [cursorGuardValue,old,actual,found,fieldList] using continues
  have currentHeader : ctx.nextPeer.isNone = true → devicePrefixSpace current ≤ NLMSG_GOODSIZE := by
    simpa only [space] using headerFits
  have scanEq : mixedPeerScan current values nodes rows ctx ctx.nextPeer
      {cursorHeaderSkb current ctx {} with room := (cursorHeaderSkb current ctx {}).room-4} #[] =
      mixedPeerScan base peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom base ctx} #[] := by
    rw [mixedPageHeader_exact current ctx currentHeader]
    simpa only [values,mixedPageRoom,space] using mixedPeerScan_refcounts base current fieldSeq peers refs nodes
      rows ctx ctx.nextPeer {room := mixedPageRoom current ctx} #[]
  have ready := cursorHeld_step_ready base current ctx.nextPeer _ held oldData newData
  refine ⟨cursorHeld_step base current ctx.nextPeer _ held oldData
    (fun id eq => let ⟨p,found,_,_⟩ := newData id eq; ⟨p,found⟩),?_⟩
  have call := wgGetDeviceDump_mixed_returns current values nodes rows ctx prev
    currentResidents currentReadable currentSelected currentSequence currentIds currentOld currentContinues currentHeader
  simp only [scanEq] at call
  have result := call ready.1 ready.2
  simpa only [attrs,generation,cursorCallResult] using result

end Leanux.Proofs.WG.Config
