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

/-- Consecutive original calls with read-only entry observations. No handshake
installation or other operation is inserted between the calls. -/
def observedSessionCalls (pids : List PeerId) : WG.M (List SessionAllocationCall) :=
  pids.mapM fun pid => do
    let entry ← Campaign2.read
    let ok ← beginSession pid
    return ⟨pid, entry, ok⟩

/-- Exact erasure retains every original error, including absent peers and
stopped session suffixes, rather than returning a partial observation list. -/
theorem observedSessionCalls_erase (pids : List PeerId) :
    (do let calls ← observedSessionCalls pids
        pure (calls.map SessionAllocationCall.result)) = pids.mapM beginSession := by
  induction pids with
  | nil => rfl
  | cons pid rest ih =>
    simp only [observedSessionCalls, List.mapM_cons, bind_assoc, pure_bind,
      List.map_cons] at ih ⊢
    simp only [← ih]
    simp only [bind_assoc, pure_bind]
    rfl

theorem observedSessionCalls_facts (pids : List PeerId) (d : Device)
    (bound : KeypairStoreBounded d) :
    Campaign2.Ensures (observedSessionCalls pids) (fun s => s.wg.device = some d)
      (SessionAllocationSequenceFacts d pids) := by
  induction pids generalizing d with
  | nil =>
    intro w ambient calls out after pre run
    change Except.ok (([], w), ambient) = .ok ((calls, out), after) at run
    cases run
    exact sessionAllocationSequence_nil d (snapshot w ambient) pre bound
  | cons pid rest ih =>
    intro w ambient calls out after pre run
    rw [observedSessionCalls, List.mapM_cons] at run
    simp only [bind_assoc, pure_bind] at run
    change (((beginSession pid).run w).run ambient >>= fun ((ok, middle), nextAmbient) =>
      ((observedSessionCalls rest).run middle).run nextAmbient >>= fun ((tail, finish), finalAmbient) =>
        Except.ok ((SessionAllocationCall.mk pid (snapshot w ambient) ok :: tail, finish), finalAmbient)) =
      .ok ((calls, out), after) at run
    cases headRun : ((beginSession pid).run w).run ambient with
    | error stop => rw [headRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨ok, middle⟩, nextAmbient⟩ := pair
      simp only [headRun, Bind.bind, Except.bind] at run
      obtain ⟨next, device, bounded, cursor, fresh⟩ :=
        beginSession_allocation_normal pid d bound w ambient ok middle nextAmbient pre headRun
      cases tailRun : ((observedSessionCalls rest).run middle).run nextAmbient with
      | error stop => rw [tailRun] at run; cases run
      | ok pair =>
        obtain ⟨⟨tail, finish⟩, finalAmbient⟩ := pair
        rw [tailRun] at run
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        exact sessionAllocationSequence_cons pid (snapshot w ambient) d next ok rest tail
          (snapshot finish finalAmbient) pre bound cursor
          (ih next bounded middle nextAmbient tail finish finalAmbient device tailRun)

end Leanux.Proofs.WG.Index
