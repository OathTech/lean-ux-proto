import Leanux.Proofs.WG.Config.CursorCallbackModel
import Leanux.Proofs.WG.Config.CursorCallbackSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

theorem fixedPeersRun_native (d : Device) (peers : PeerId → Peer) (ids : List PeerId)
    (residents : ∀ pid ∈ ids, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ ids, (peers pid).allowedipsList = [])
    (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    Returns (forIn ids (ctx,cursor,skb,true,prior) deviceDumpPeersStep)
      (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = fixedPeersRun peers ids ctx cursor skb prior) := by
  induction ids generalizing ctx cursor skb prior with
  | nil =>
    intro g ambient device
    exact ⟨_,g,ambient,rfl,device,rfl⟩
  | cons pid ids ih =>
    intro g ambient device
    let first : Ambient := {ambient with steps := ambient.steps.push {
      decision := .dumpPeerIter,outcome := true,netRx := ambient.netRxSection}}
    obtain ⟨value,middle,after,run,same,valueEq⟩ :=
      multipart_getter_returns pid d (peers pid) ctx skb (fixedPeerResult (peers pid) ctx skb)
        (residents pid (by simp))
        (dumpTail_fixed_room (peers pid) ctx skb fresh (empty pid (by simp)) (fun g => g.dev = some d))
        g first device
    subst value
    by_cases fits : peerFixedSpace (peers pid) ≤ skb.room
    · let inputs : Ambient := {after with steps := after.steps.push {
        decision := .dumpGetPeerFail,outcome := false,netRx := after.netRxSection}}
      obtain ⟨result,final,last,tailRun,finalDevice,resultEq⟩ :=
        ih (fun q member => residents q (by simp [member]))
          (fun q member => empty q (by simp [member]))
          {ctx with nextAllowedip := none,allowedipsSeq := 0} rfl (some pid)
          {skb with room := skb.room-peerFixedSpace (peers pid)}
          (prior.push {publicKey := hexKey (peers pid).remoteStatic,attrs := peerFixedAttrs (peers pid)})
          middle inputs same
      refine ⟨result,final,last,?_,finalDevice,?_⟩
      · rw [List.forIn_cons]
        simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
        change (((getPeerDump pid ctx skb).run g).run first >>= _) = _
        rw [run]
        simpa [fixedPeerResult,fits] using tailRun
      · simpa [fixedPeersRun,fits] using resultEq
    · let inputs : Ambient := {after with steps := after.steps.push {
        decision := .dumpGetPeerFail,outcome := true,netRx := after.netRxSection}}
      refine ⟨(ctx,cursor,skb,false,prior),middle,inputs,?_,same,?_⟩
      · rw [List.forIn_cons]
        simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
        change (((getPeerDump pid ctx skb).run g).run first >>= _) = _
        rw [run]
        simp [fixedPeerResult,fits]
        rfl
      · simp [fixedPeersRun,fits]

/-- The completed-prefix cursor is initial or an actually visited list entry. -/
theorem fixedPeersRun_cursors (peers : PeerId → Peer) (ids : List PeerId)
    (ctx : DumpCtx) (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    (fixedPeersRun peers ids ctx cursor skb prior).1.nextPeer = ctx.nextPeer ∧
    ((fixedPeersRun peers ids ctx cursor skb prior).2.1 = cursor ∨
      ∃ pid ∈ ids, (fixedPeersRun peers ids ctx cursor skb prior).2.1 = some pid) := by
  induction ids generalizing ctx cursor skb prior with
  | nil => exact ⟨rfl,Or.inl rfl⟩
  | cons pid ids ih =>
    simp only [fixedPeersRun]
    split
    · obtain ⟨same,origin⟩ := ih {ctx with nextAllowedip := none,allowedipsSeq := 0}
        (some pid) {skb with room := skb.room-peerFixedSpace (peers pid)}
        (prior.push {publicKey := hexKey (peers pid).remoteStatic,attrs := peerFixedAttrs (peers pid)})
      refine ⟨same,Or.inr ?_⟩
      rcases origin with origin | ⟨other,member,origin⟩
      · exact ⟨pid,by simp,origin⟩
      · exact ⟨other,by simp [member],origin⟩
    · exact ⟨rfl,Or.inl rfl⟩

end Leanux.Proofs.WG.Config
