import Leanux.Proofs.WG.Config.CursorLoopSource
import Leanux.Proofs.WG.Config.CursorHandoffSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

theorem cursorLoopFinish_normal (d : Device) (peers : PeerId → Peer) (ids : List PeerId)
    (residents : ∀ pid ∈ ids, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ ids, (peers pid).allowedipsList = [])
    (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p)
    (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb) :
    let state := fixedPeersRun peers ids ctx ctx.nextPeer skb #[]
    Ensures (cursorLoopFinish d ids ctx flags attrs skb) (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs state.1 state.2.1 state.2.2.1 state.2.2.2.1 (some state.2.2.2.2) ∧
        g.dev = some (cursorReleased (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)) state.1.nextPeer)) := by
  dsimp only
  intro g ambient result final after device run
  obtain ⟨value,middle,remaining,loopRun,same,valueEq⟩ :=
    fixedPeersRun_native d peers ids residents empty ctx fresh ctx.nextPeer skb #[] g ambient device
  subst value
  have cursorFacts := fixedPeersRun_cursors peers ids ctx ctx.nextPeer skb #[]
  generalize stateEq : fixedPeersRun peers ids ctx ctx.nextPeer skb #[] = state at loopRun cursorFacts ⊢
  obtain ⟨outCtx,cursor,outSkb,done,parts⟩ := state
  have newResident : ∀ pid, cursor = some pid → ∃ p, d.peers[pid]? = some p := by
    intro pid found
    rcases cursorFacts.2 with prior | ⟨other,member,foundOther⟩
    · exact oldResident pid (prior.symm.trans found)
    · have equal : other = pid := Option.some.inj (foundOther.symm.trans found)
      subst other
      exact ⟨peers pid,residents pid member⟩
  have oldResident' : ∀ pid, outCtx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p := by
    intro pid found
    exact oldResident pid (cursorFacts.1.symm.trans found)
  have finish := cursorDumpFinish_normal d flags attrs outCtx cursor outSkb done (some parts)
    newResident oldResident'
  simp only [cursorLoopFinish] at run
  change (((forIn ids (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep).run g).run ambient >>= _) = _ at run
  rw [loopRun] at run
  cases done with
  | false => exact finish middle remaining result final after same run
  | true =>
    let next : Ambient := {remaining with steps := remaining.steps.push {
      decision := .dumpPeerIter,outcome := false,netRx := remaining.netRxSection}}
    exact finish middle next result final after same run

theorem cursorDumpGuard_returns (d : Device) (ctx : DumpCtx)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p) :
    Returns (cursorDumpGuard d ctx) (fun g => g.dev = some d)
      (fun value g => value = cursorGuardValue d ctx ∧ g.dev = some d) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome,netRx := a.netRxSection}}
  cases empty : d.peerList.isEmpty with
  | true =>
    refine ⟨true,g,mark ambient .dumpPeerListEmpty true,?_,?_,device⟩
    · simp [cursorDumpGuard,WG.orM,branch,AmbientM.branch,empty,mark]
      rfl
    · simp [cursorGuardValue,empty]
  | false =>
    cases old : ctx.nextPeer with
    | none =>
      refine ⟨false,g,mark (mark ambient .dumpPeerListEmpty false) .dumpCursorSet false,?_,?_,device⟩
      · simp [cursorDumpGuard,WG.orM,WG.andM,branch,AmbientM.branch,empty,old,mark]
        rfl
      · simp [cursorGuardValue,empty,old]
    | some pid =>
      obtain ⟨p,resident⟩ := oldResident pid old
      refine ⟨p.isDead,g,mark (mark (mark ambient .dumpPeerListEmpty false) .dumpCursorSet true) .dumpCursorDead p.isDead,?_,?_,device⟩
      · simp [cursorDumpGuard,WG.orM,WG.andM,branch,AmbientM.branch,empty,old,getPeer,getDev,device,resident,mark]
        rfl
      · simp [cursorGuardValue,empty,old,resident]

theorem cursorDumpBody_normal (d : Device) (peers : PeerId → Peer) (ctx : DumpCtx)
    (residents : ∀ pid ∈ cursorSelected d ctx, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ cursorSelected d ctx, (peers pid).allowedipsList = [])
    (fresh : ctx.nextAllowedip = none)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p)
    (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb) :
    let state := cursorBodyState d peers ctx {skb with room := skb.room-4}
    Ensures (cursorDumpBody d ctx flags attrs skb) (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 ∧
        g.dev = some (cursorReleased (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)) state.1.nextPeer)) := by
  dsimp only
  intro g ambient result final after device run
  by_cases small : skb.room < 4
  · simp [cursorDumpBody,NlSkb.put,nlaTotal,small,branch,AmbientM.branch,unsupported,AmbientM.unsupported] at run
    cases run
  · let before : Ambient := {ambient with steps := ambient.steps.push {
      decision := .dumpNoPeersNest,outcome := false,netRx := ambient.netRxSection}}
    obtain ⟨value,middle,remaining,guardRun,valueEq,same⟩ := cursorDumpGuard_returns d ctx oldResident g before device
    subst value
    simp [cursorDumpBody,NlSkb.put,nlaTotal,small,branch,AmbientM.branch] at run
    change (((cursorDumpGuard d ctx).run g).run before >>= _) = _ at run
    rw [guardRun] at run
    cases decision : cursorGuardValue d ctx with
    | true =>
      rw [decision] at run
      have finish := cursorDumpFinish_normal d flags attrs ctx ctx.nextPeer
        {skb with room := skb.room-4} true none oldResident oldResident
        middle remaining result final after same run
      simpa [cursorBodyState,decision] using finish
    | false =>
      rw [decision] at run
      have loop := cursorLoopFinish_normal d peers (cursorSelected d ctx) residents empty ctx fresh oldResident
        flags attrs {skb with room := skb.room-4} middle remaining result final after same
          (by cases cursor : ctx.nextPeer <;> simpa [cursorSelected, cursor] using run)
      simpa [cursorBodyState,decision] using loop

end Leanux.Proofs.WG.Config
