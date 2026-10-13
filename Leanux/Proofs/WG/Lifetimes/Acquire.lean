import Leanux.Proofs.WG.Lifetimes.MixedFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Reference acquisition's two reads and conditional write, including
pending-worker and refcount rejection prefixes. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def peerGetEvents (id : PeerId) (w : World) : List Peers.PeerEvent :=
  match w.k.wg.bind (fun d => d.peers[id]?) with
  | none => []
  | some p =>
    if p.handshakePending && !w.queuedThisCall.contains id then [.read id p.internalId]
    else [.read id p.internalId, .read id p.internalId] ++
      if p.refcount = 0 ∨ p.refcount + 1 ≥ 2 ^ 31 then [] else [.write id p.internalId]

theorem peerGetLocal_events (id : PeerId) (w : World) (h : List Peers.PeerEvent) :
    (runPrefix (peerGetLocal id) w h).2 = h ++ peerGetEvents id w := by
  cases hd : w.k.wg with
  | none => simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
      runPrefix_bind, getPeer, getDev, getK, hd, invariant]
  | some d =>
    cases hp : d.peers[id]? with
    | none => simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
        runPrefix_bind, getPeer, getDev, getK, hd, hp, invariant]
    | some p =>
      by_cases hpend : p.handshakePending = true ∧ ¬ id ∈ w.queuedThisCall
      · simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
          runPrefix_bind, getPeer, getDev, getK, hd, hp, hpend, unsupported]
      · by_cases hz : p.refcount = 0
        · simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
            runPrefix_bind, getPeer, getDev, getK, hd, hp, hpend, hz,
            refcountInc, branch, branchCmp, unsupported, List.append_assoc]
        · by_cases ho : p.refcount + 1 ≥ 2 ^ 31
          all_goals have hwrap : (2147483647 ≤ p.refcount) ↔ (p.refcount + 1 ≥ 2 ^ 31) := by omega
          all_goals simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
            runPrefix_bind, getPeer, getDev, getK, hd, hp, hpend, hz, ho, hwrap,
            refcountInc, branch, branchCmp, unsupported, setPeer, modifyDev, modifyK,
            List.append_assoc]

theorem peerGetLocal_run (id : PeerId) (w : World) (h : List Peers.PeerEvent) :
    runPrefix (peerGetLocal id) w h = ((peerGet id).run w, h ++ peerGetEvents id w) :=
  Prod.ext (peerGetLocal_erases id w h) (peerGetLocal_events id w h)

theorem peerGetEvents_preserves (id : PeerId) (w : World) (h : List Peers.PeerEvent)
    (hi : Peers.AccessInv h w) : Peers.AccessInv (h ++ peerGetEvents id w) w := by
  cases hp : w.k.wg.bind (fun d => d.peers[id]?) with
  | none => simpa [peerGetEvents, hp] using hi
  | some p =>
    have live : (Peers.snapshot w).slots id = some p.internalId := by
      change (w.k.wg.bind (fun d => d.peers[id]?)).map (·.internalId) = _
      rw [hp]; rfl
    have hn : ¬ AccessEvent.Released h p.internalId := fun hr => hi.2.2 _ hr id live
    have one := AccessEvent.safe_append_read (slot := id) hi.1 hn
    have two := AccessEvent.safe_append_read (slot := id) one
      (by simpa only [AccessEvent.released_append_read] using hn)
    have three := AccessEvent.safe_append_write (slot := id) two
      (by simpa only [AccessEvent.released_append_read] using hn)
    by_cases pending : p.handshakePending = true ∧ ¬ id ∈ w.queuedThisCall
    · simpa [peerGetEvents, hp, pending, Peers.AccessInv] using
        (show Peers.AccessInv (h ++ [.read id p.internalId]) w from
          ⟨one, hi.2.1, fun s hs => hi.2.2 s (AccessEvent.released_append_read.mp hs)⟩)
    · by_cases bad : p.refcount = 0 ∨ p.refcount + 1 ≥ 2 ^ 31
      · have bad' : p.refcount = 0 ∨ 2147483647 ≤ p.refcount := by omega
        simpa [peerGetEvents, hp, pending, bad, bad', List.append_assoc, Peers.AccessInv] using
          (show Peers.AccessInv ((h ++ [.read id p.internalId]) ++ [.read id p.internalId]) w from
            ⟨two, hi.2.1, fun s hs => hi.2.2 s (by simpa only [AccessEvent.released_append_read, AccessEvent.released_append_write] using hs)⟩)
      · have bad' : ¬(p.refcount = 0 ∨ 2147483647 ≤ p.refcount) := by omega
        simpa [peerGetEvents, hp, pending, bad, bad', List.append_assoc, Peers.AccessInv] using
          (show Peers.AccessInv (((h ++ [.read id p.internalId]) ++ [.read id p.internalId]) ++
            [.write id p.internalId]) w from
              ⟨three, hi.2.1, fun s hs => hi.2.2 s (by simpa only [AccessEvent.released_append_read, AccessEvent.released_append_write] using hs)⟩)

theorem peerGetLocal_preserves (id : PeerId) :
    PrefixPreserves Peers.AccessInv AccessEvent.Safe (peerGetLocal id) := by
  intro w h hi
  rw [peerGetLocal_run]
  have hn := peerGetEvents_preserves id w h hi
  refine ⟨peerGetEvents id w, rfl, hn.1, ?_⟩
  cases hr : (peerGet id).run w with
  | error e => trivial
  | ok out =>
    have retained := Peers.peerGet_retained id w out.1 out.2 hr
    exact ⟨hn.1, retained.unique hn.2.1, fun s hs => retained.absent (hn.2.2 s hs)⟩

theorem peerGet_otherResidents (id : PeerId) : SameView otherResidents (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountInc, branch, branchCmp, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold otherResidents at *
  all_goals unfold keypairResidents packetResidents at *
  all_goals simp_all

theorem peerGetMixed_preserves (id : PeerId) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (peerGetMixed id) :=
  peerFocus_preserves (peerGetLocal_preserves id) (peerGetLocal_erases id)
    (peerGet_otherResidents id)

end Leanux.Proofs.WG.Lifetimes
