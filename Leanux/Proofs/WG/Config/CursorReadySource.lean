import Leanux.Proofs.WG.Config.CursorReacquireEffects
import Leanux.Proofs.WG.Config.TwoPageCallbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Total original finalizer under exact acquire/release reference data.
The release reads the post-acquisition resident, including coincident cursors.
NULL cursors and completion require no unused acquisition premise. -/
theorem cursorFinish_ready_returns (d : Device) (flags : Nat) (attrs : List (String × Json))
    (ctx : DumpCtx) (next : Option PeerId) (skb : NlSkb) (done : Bool)
    (parts : Option (Array PeerDumpAttrs))
    (acquireReady : ∀ id, (if done then none else next) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31)
    (releaseReady : ∀ id, ctx.nextPeer = some id →
      ∃ p, (cursorAcquired d (if done then none else next)).peers[id]? = some p ∧
        1 < p.refcount) :
    Returns (cursorDumpFinish d flags attrs ctx next skb done parts)
      (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs ctx next skb done parts ∧
        g.dev = some (cursorHandoff d ctx.nextPeer (if done then none else next))) := by
  have put (current : Device)
      (ready : ∀ id, ctx.nextPeer = some id →
        ∃ p, current.peers[id]? = some p ∧ 1 < p.refcount) :
      Returns (peerPut ctx.nextPeer) (fun g => g.dev = some current)
        (fun _ g => g.dev = some (cursorReleased current ctx.nextPeer)) := by
    cases old : ctx.nextPeer with
    | none =>
      intro g ambient device
      refine ⟨(),g,{ambient with steps := ambient.steps.push {decision := .peerPutNull,outcome := true,netRx := ambient.netRxSection}},?_,?_⟩
      · simp [peerPut,branch,AmbientM.branch]
        rfl
      · exact device
    | some id =>
      obtain ⟨p,found,retained⟩ := ready id old
      have notLast : p.refcount ≠ 1 := by omega
      have actual := (returns_iff _ _ _).mpr
        (peerPut_retained_returns id current p found retained)
      simpa [cursorReleased,found,Index.releasedPeerDevice,notLast,withPeer] using actual
  let mark (a : Ambient) (site : Decision) (value : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome := value,netRx := a.netRxSection}}
  cases done with
  | false =>
    cases next with
    | none =>
      intro g ambient device
      let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor false
      obtain ⟨value,final,after,run,post⟩ := put d (by simpa [cursorAcquired] using releaseReady) g before device
      cases value
      let remaining := mark (mark after .dumpRetErr false) .dumpDone false
      refine ⟨cursorCallResult d flags attrs ctx none skb false parts,final,remaining,?_,rfl,post⟩
      simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch]
      change (((peerPut ctx.nextPeer).run g).run before >>= _) = _
      rw [run]
      simp [cursorCallResult,remaining,mark]
    | some id =>
      obtain ⟨p,found,positive,bounded⟩ := acquireReady id rfl
      intro g ambient device
      let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor true
      obtain ⟨value,middle,inputs,getRun,midDevice⟩ :=
        TwoPage.peerGet_returns id d p found positive bounded g before device
      cases value
      obtain ⟨value,final,after,putRun,post⟩ :=
        put (cursorAcquired d (some id)) releaseReady middle inputs midDevice
      cases value
      let remaining := mark (mark after .dumpRetErr false) .dumpDone false
      refine ⟨cursorCallResult d flags attrs ctx (some id) skb false parts,final,remaining,?_,rfl,post⟩
      simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch]
      change (((peerGet id).run g).run before >>= _) = _
      rw [getRun]
      change (((peerPut ctx.nextPeer).run middle).run inputs >>= _) = _
      rw [putRun]
      simp [cursorCallResult,remaining,mark]
  | true =>
    intro g ambient device
    let before := mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone false
    obtain ⟨value,final,after,run,post⟩ := put d (by simpa [cursorAcquired] using releaseReady) g before device
    cases value
    let remaining := mark (mark after .dumpRetErr false) .dumpDone true
    refine ⟨cursorCallResult d flags attrs ctx next skb true parts,final,remaining,?_,rfl,post⟩
    simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch]
    change (((peerPut ctx.nextPeer).run g).run before >>= _) = _
    rw [run]
    simp [cursorCallResult,remaining,mark]

/-- Local source refusal when a held cursor is reacquired at the signed-count
boundary. The initial acquisition's baseline bound holds, but the second does
not. This arbitrary-state source fact claims no initialized whole-dump history. -/
theorem cursorFinish_reacquire_overflow (base : Device) (id : PeerId) (p : Peer)
    (resident : base.peers[id]? = some p) (count : p.refcount = 2^31-2)
    (flags : Nat) (attrs : List (String × Json)) (ctx : DumpCtx)
    (skb : NlSkb) (parts : Option (Array PeerDumpAttrs))
    (g : WGWorld) (ambient : Ambient)
    (device : g.dev = some (cursorAcquired base (some id))) :
    ((cursorDumpFinish (cursorAcquired base (some id)) flags attrs
      {ctx with nextPeer := some id} (some id) skb false parts).run g).run ambient =
      .error (.outsideDomain (s!"{Decision.refcountAddWraps.info.file}:{Decision.refcountAddWraps.info.line}") "refcount_warn_saturate (overflow)") := by
  simp [cursorDumpFinish,WG.andM,peerGet,requireNotPending,getPeer,getDev,device,
    cursorAcquired,resident,refcountInc,count,branch,branchCmp,AmbientM.branch,
    AmbientM.branchCmp,unsupported,AmbientM.unsupported]
  rfl

end Leanux.Proofs.WG.Config
