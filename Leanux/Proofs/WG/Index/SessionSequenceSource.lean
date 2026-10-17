import Leanux.Proofs.WG.Index.SessionSequenceEffects
import Leanux.Proofs.WG.Index.SessionAllocationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2

/-- A normal original run passed its first peer read before any session change. -/
theorem beginSession_entry_resident (pid : PeerId) (d : Device)
    (w out : WGWorld) (ambient after : Ambient) (ok : Bool) (pre : w.dev = some d)
    (run : ((beginSession pid).run w).run ambient = .ok ((ok, out), after)) :
    ∃ p, d.peers[pid]? = some p := by
  cases found : d.peers[pid]? with
  | some p => exact ⟨p, rfl⟩
  | none =>
    simp [beginSession, getPeer, getDev, pre, found,
      invariant, AmbientM.invariant, StateT.run_bind] at run
    change Except.error (Stop.invariant s!"dangling peer {pid}") = Except.ok ((ok, out), after) at run
    cases run

theorem beginSession_allocation_normal (pid : PeerId) (d : Device)
    (bound : KeypairStoreBounded d) :
    Noise.Ensures (beginSession pid) (fun w => w.dev = some d)
      (fun ok w => ∃ final, w.dev = some final ∧ KeypairStoreBounded final ∧
        final.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) ∧
        d.keypairs[d.nextKeypairId]? = none) := by
  intro w ambient ok out after pre run
  obtain ⟨p, resident⟩ := beginSession_entry_resident pid d w out ambient after ok pre run
  exact beginSession_allocation pid d p resident bound w ambient ok out after pre run

/-- Consecutive original calls with full Product entry observations. No handshake
installation or other operation is inserted between the calls. -/
def observedSessionCalls (pids : List PeerId) : Leanux.M (List SessionAllocationCall) :=
  pids.mapM fun pid => do
    let entry ← Campaign2.Product.read
    let ok ← liftWG (beginSession pid)
    return ⟨pid, entry, ok⟩

/-- Exact erasure retains every original error, including absent peers and
stopped session suffixes, rather than returning a partial observation list. -/
theorem observedSessionCalls_erase (pids : List PeerId) :
    (do let calls ← observedSessionCalls pids
        pure (calls.map SessionAllocationCall.result)) = liftWG (pids.mapM beginSession) := by
  have liftBind {α β : Type} (action : WG.M α) (next : α → WG.M β) :
      liftWG (do let result ← action; next result) =
        (do let result ← liftWG action; liftWG (next result)) := by
    funext w
    change (((action.run w.wg).run w.ambient >>= fun ((value, current), ambient) =>
      ((next value).run current).run ambient) >>= fun ((value, current), ambient) =>
        Except.ok (value, {w with wg := current, ambient})) =
      (((action.run w.wg).run w.ambient >>= fun ((value, current), ambient) =>
        Except.ok (value, {w with wg := current, ambient})) >>= fun (value, middle) =>
          ((next value).run middle.wg).run middle.ambient >>= fun ((result, current), ambient) =>
            Except.ok (result, {middle with wg := current, ambient}))
    simp only [bind_assoc]
    cases executed : (action.run w.wg).run w.ambient with
    | error stop => rfl
    | ok pair =>
      obtain ⟨⟨value, current⟩, ambient⟩ := pair
      rfl
  have liftPure {α : Type} (value : α) :
      liftWG (pure value : WG.M α) = (pure value : Leanux.M α) := rfl
  induction pids with
  | nil => rfl
  | cons pid rest ih =>
    simp only [observedSessionCalls, List.mapM_cons, liftBind, liftPure, bind_assoc, pure_bind,
      List.map_cons] at ih ⊢
    simp only [← ih]
    simp only [bind_assoc, pure_bind]
    rfl

theorem observedSessionCalls_facts (pids : List PeerId) (d : Device)
    (bound : KeypairStoreBounded d) :
    Campaign2.Product.Ensures (observedSessionCalls pids) (fun s => s.wg.device = some d)
      (SessionAllocationSequenceFacts d pids) := by
  induction pids generalizing d with
  | nil =>
    intro w calls out pre run
    change Except.ok ([], w) = .ok (calls, out) at run
    cases run
    exact sessionAllocationSequence_nil d (Campaign2.Product.snapshot w) pre bound
  | cons pid rest ih =>
    intro w calls out pre run
    rw [observedSessionCalls, List.mapM_cons] at run
    simp only [bind_assoc, pure_bind] at run
    change ((liftWG (beginSession pid)).run w >>= fun (ok, middle) =>
      (observedSessionCalls rest).run middle >>= fun (tail, finish) =>
        Except.ok (SessionAllocationCall.mk pid (Campaign2.Product.snapshot w) ok :: tail, finish)) =
      .ok (calls, out) at run
    cases headRun : (liftWG (beginSession pid)).run w with
    | error stop => rw [headRun] at run; cases run
    | ok pair =>
      obtain ⟨ok, middle⟩ := pair
      simp only [headRun, Bind.bind, Except.bind] at run
      have head : ∃ next, middle.wg.dev = some next ∧ KeypairStoreBounded next ∧
          next.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) ∧
          d.keypairs[d.nextKeypairId]? = none := by
        change (((beginSession pid).run w.wg).run w.ambient >>= fun ((value, current), ambient) =>
          Except.ok (value, {w with wg := current, ambient})) = .ok (ok, middle) at headRun
        cases nativeRun : ((beginSession pid).run w.wg).run w.ambient with
        | error stop => rw [nativeRun] at headRun; cases headRun
        | ok pair =>
          obtain ⟨⟨value, current⟩, ambient⟩ := pair
          rw [nativeRun] at headRun
          cases headRun
          exact beginSession_allocation_normal pid d bound w.wg w.ambient _ current ambient pre nativeRun
      obtain ⟨next, device, bounded, cursor, fresh⟩ := head
      cases tailRun : (observedSessionCalls rest).run middle with
      | error stop => rw [tailRun] at run; cases run
      | ok pair =>
        obtain ⟨tail, finish⟩ := pair
        rw [tailRun] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        exact sessionAllocationSequence_cons pid (Campaign2.Product.snapshot w) d next ok rest tail
          (Campaign2.Product.snapshot finish) pre bound cursor
          (ih next bounded middle tail finish device tailRun)

end Leanux.Proofs.WG.Index
