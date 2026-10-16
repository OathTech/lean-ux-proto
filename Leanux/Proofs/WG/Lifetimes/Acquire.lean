import Leanux.Proofs.WG.Lifetimes.MixedFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Reference acquisition's read and conditional write, including refcount rejection prefixes. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def peerGetEvents (id : PeerId) (w : WGWorld) : List Peers.PeerEvent :=
  match w.dev.bind (fun d => d.peers[id]?) with
  | none => []
  | some p =>
    [.read id p.internalId] ++
      if p.refcount = 0 ∨ p.refcount + 1 ≥ 2 ^ 31 then [] else [.write id p.internalId]

theorem peerGetLocal_events (id : PeerId) (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    (runStatePrefix (peerGetLocal id) w ambient h).2 = h ++ peerGetEvents id w := by
  cases hd : w.dev with
  | none => simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
      runStatePrefix_bind, getPeer, getDev, hd, invariant, AmbientM.invariant, liftWGPrefix] <;> rfl
  | some d =>
    cases hp : d.peers[id]? with
    | none => simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
        runStatePrefix_bind, getPeer, getDev, hd, hp, invariant, AmbientM.invariant, liftWGPrefix] <;> rfl
    | some p =>
      by_cases hz : p.refcount = 0
      · simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
          runStatePrefix_bind, getPeer, getDev, hd, hp, hz,
          refcountInc, branch, branchCmp, unsupported, AmbientM.branch, AmbientM.branchCmp,
          AmbientM.unsupported, liftWGPrefix, StateT.run_bind, StateT.run_pure, List.append_assoc] <;> rfl
      · by_cases ho : p.refcount + 1 ≥ 2 ^ 31
        all_goals have hwrap : (2147483647 ≤ p.refcount) ↔ (p.refcount + 1 ≥ 2 ^ 31) := by omega
        all_goals simp [peerGetLocal, peerGetEvents, Peers.requireNotPendingPrefix,
          runStatePrefix_bind, getPeer, getDev, hd, hp, hz, ho, hwrap,
          refcountInc, branch, branchCmp, unsupported, setPeer, modifyDev,
          AmbientM.branch, AmbientM.branchCmp, AmbientM.unsupported, liftWGPrefix,
          StateT.run_bind, StateT.run_pure, List.append_assoc] <;> rfl

theorem peerGetLocal_run (id : PeerId) (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    runStatePrefix (peerGetLocal id) w ambient h = (((peerGet id).run w).run ambient, h ++ peerGetEvents id w) :=
  Prod.ext (peerGetLocal_erases id w ambient h) (peerGetLocal_events id w ambient h)

theorem peerGetEvents_preserves (id : PeerId) (w : WGWorld) (h : List Peers.PeerEvent)
    (hi : Peers.AccessInv h w) : Peers.AccessInv (h ++ peerGetEvents id w) w := by
  cases hp : w.dev.bind (fun d => d.peers[id]?) with
  | none => simpa [peerGetEvents, hp] using hi
  | some p =>
    have live : (Peers.snapshot w).slots id = some p.internalId := by
      change (w.dev.bind (fun d => d.peers[id]?)).map (·.internalId) = _
      rw [hp]; rfl
    have hn : ¬ AccessEvent.Released h p.internalId := fun hr => hi.2.2 _ hr id live
    have one := AccessEvent.safe_append_read (slot := id) hi.1 hn
    have two := AccessEvent.safe_append_write (slot := id) one
      (by simpa only [AccessEvent.released_append_read] using hn)
    by_cases bad : p.refcount = 0 ∨ p.refcount + 1 ≥ 2 ^ 31
    · have bad' : p.refcount = 0 ∨ 2147483647 ≤ p.refcount := by omega
      simpa [peerGetEvents, hp, bad, bad', Peers.AccessInv] using
        (show Peers.AccessInv (h ++ [.read id p.internalId]) w from
          ⟨one, hi.2.1, fun s hs => hi.2.2 s (AccessEvent.released_append_read.mp hs)⟩)
    · have bad' : ¬(p.refcount = 0 ∨ 2147483647 ≤ p.refcount) := by omega
      simpa [peerGetEvents, hp, bad, bad', List.append_assoc, Peers.AccessInv] using
        (show Peers.AccessInv ((h ++ [.read id p.internalId]) ++ [.write id p.internalId]) w from
          ⟨two, hi.2.1, fun s hs => hi.2.2 s (by simpa only [AccessEvent.released_append_read,
            AccessEvent.released_append_write] using hs)⟩)

theorem peerGetLocal_preserves (id : PeerId) :
    StatePrefixPreserves (fun h w _ => Peers.AccessInv h w) AccessEvent.Safe (peerGetLocal id) := by
  intro w ambient h hi
  change ∃ suffix, _ ∧ _ ∧ _
  rw [show runPrefix ((peerGetLocal id).run w) ambient h =
      runStatePrefix (peerGetLocal id) w ambient h from rfl, peerGetLocal_run]
  have hn := peerGetEvents_preserves id w h hi
  refine ⟨peerGetEvents id w, rfl, hn.1, ?_⟩
  cases hr : ((peerGet id).run w).run ambient with
  | error e => trivial
  | ok out =>
    have retained := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Peers.peerGet_retained id) w ambient out.1.1 out.1.2 out.2 hr
    exact ⟨hn.1, retained.unique hn.2.1, fun s hs => retained.absent (hn.2.2 s hs)⟩

theorem peerGet_otherResidents (id : PeerId) : SameView otherResidents (peerGet id) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountInc, branch, branchCmp, invariant, unsupported,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold otherResidents at *
  all_goals unfold keypairResidents packetResidents at *
  all_goals simp_all

theorem peerGetMixed_preserves (id : PeerId) :
    StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe (peerGetMixed id) :=
  peerStateFocus_preserves (peerGetLocal_preserves id) (peerGetLocal_erases id)
    (peerGet_otherResidents id)

end Leanux.Proofs.WG.Lifetimes
