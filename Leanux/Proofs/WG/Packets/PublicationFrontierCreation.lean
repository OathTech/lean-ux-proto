import Leanux.Proofs.WG.Packets.PublicationFrontier

/-! Fresh peer creation may overwrite the frontier slot, but an already
published packet is strictly below that slot. Absence between publication and
creation is permitted; only the packet-selected peer identity is transported. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues PublicationIdentity

/-- Concrete retained packet cells, a same-epoch monotone frontier, and
identities below the old frontier suffice. New resident peers need no old mate. -/
theorem Inv.transport_below (hi : Inv history w)
    (packets : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w)
    (monotone : FrontiersLe w v)
    (peers : ∀ before after, w.dev = some before → v.dev = some after →
      before.ifindex = after.ifindex → CurrentIdentity.BelowRetained before after) : Inv history v := by
  refine ⟨?_,hi.2.transport packets monotone⟩
  intro id pkt cell crypted
  have old : (RxDisposition.nativeRxStore w).2 id = some pkt :=
    (congrFun (congrArg Prod.snd packets) id).symm.trans cell
  obtain ⟨pre,post,r,out,pid,published,ambient,position,source,retained⟩ := hi.1 id pkt old crypted
  have original : (w.dev.bind fun d => d.rxSkbs[id]?) = some pkt := old
  obtain ⟨before,hb,hpkt⟩ := Option.bind_eq_some_iff.mp original
  have same : pkt = {out with state := .crypted} := Option.some.inj (old.symm.trans retained.2.2.1)
  have owner : pkt.peer = pid := by rw [same]; exact retained.1.live.packet_peer
  have bound : pid < before.nextPeer := by
    rw [← owner]
    exact hi.2 before hb id pkt hpkt crypted
  refine ⟨pre,post,r,out,pid,published,ambient,position,source,retained.transport ?_ ?_ ?_⟩
  · exact congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst packets)
  · exact congrFun (congrArg Prod.snd packets) id
  · intro after p ha hp
    have epoch : before.ifindex = after.ifindex := by
      simpa [RxDisposition.nativeRxStore,ha,hb] using (congrArg Prod.fst packets).symm
    obtain ⟨oldPeer,hpeer,identity⟩ := peers before after hb ha epoch pid p bound hp
    exact ⟨before,oldPeer,hb,hpeer,identity⟩

/-- This contract includes allocation refusal and all normal errno results.
It relies on the original creation geometry, not a vacant-frontier premise. -/
theorem peerCreate_preserves (key : Key) (psk : Option Key) (history : List RxHistory.Event) :
    Preserves (Inv history) (peerCreate key psk) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have geometry := peerCreate_geometry key psk w v result a b hr
  have rx := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.peerCreate_rx) key psk)
    w a result v b hr
  apply hi.transport_below rx
  · intro before after hb ha _
    obtain ⟨d,hd,_,_,_,next⟩ := geometry.device ha
    have eq : d = before := Option.some.inj (hd.symm.trans hb)
    subst d
    cases result with
    | error err => exact Nat.le_of_eq next.symm
    | ok pid =>
      have old : before.nextPeer = pid := by simpa [hb] using geometry.2.2
      rw [next,old]
      exact Nat.le_succ _
  · intro before after hb ha _
    exact CurrentIdentity.peerCreate_below key psk w v a b result before after hb ha hr

end Leanux.Proofs.WG.PublicationFrontier
