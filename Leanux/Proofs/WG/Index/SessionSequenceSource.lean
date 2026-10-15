import Leanux.Proofs.WG.Index.SessionSequenceEffects
import Leanux.Proofs.WG.Index.SessionAllocationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2

/-- A normal original run passed its first peer read before any session change. -/
theorem beginSession_entry_resident (pid : PeerId) (d : Device)
    (w out : World) (ok : Bool) (pre : w.k.wg = some d)
    (run : (beginSession pid).run w = .ok (ok, out)) :
    ∃ p, d.peers[pid]? = some p := by
  cases found : d.peers[pid]? with
  | some p => exact ⟨p, rfl⟩
  | none =>
    simp [beginSession, getPeer, getDev, getK, pre, found,
      invariant, StateT.run_bind] at run
    change Except.error (Stop.invariant s!"dangling peer {pid}") = Except.ok (ok, out) at run
    cases run

theorem beginSession_allocation_normal (pid : PeerId) (d : Device)
    (bound : KeypairStoreBounded d) :
    Noise.Ensures (beginSession pid) (fun w => w.k.wg = some d)
      (fun ok w => ∃ final, w.k.wg = some final ∧ KeypairStoreBounded final ∧
        final.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) ∧
        d.keypairs[d.nextKeypairId]? = none) := by
  intro w ok out pre run
  obtain ⟨p, resident⟩ := beginSession_entry_resident pid d w out ok pre run
  exact beginSession_allocation pid d p resident bound w ok out pre run

/-- Consecutive original calls with read-only entry observations. No handshake
installation or other operation is inserted between the calls. -/
def observedSessionCalls (pids : List PeerId) : M (List SessionAllocationCall) :=
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
    intro w calls out pre run
    change Except.ok ([], w) = .ok (calls, out) at run
    cases run
    exact sessionAllocationSequence_nil d (snapshot w) pre bound
  | cons pid rest ih =>
    intro w calls out pre run
    rw [observedSessionCalls, List.mapM_cons] at run
    simp only [bind_assoc, pure_bind] at run
    change ((beginSession pid).run w >>= fun pair =>
      (observedSessionCalls rest).run pair.2 >>= fun tail =>
        Except.ok (SessionAllocationCall.mk pid (snapshot w) pair.1 :: tail.1, tail.2)) =
      .ok (calls, out) at run
    cases headRun : (beginSession pid).run w with
    | error stop => rw [headRun] at run; cases run
    | ok pair =>
      obtain ⟨ok, middle⟩ := pair
      simp only [headRun, Bind.bind, Except.bind] at run
      obtain ⟨next, device, bounded, cursor, fresh⟩ :=
        beginSession_allocation_normal pid d bound w ok middle pre headRun
      cases tailRun : (observedSessionCalls rest).run middle with
      | error stop => rw [tailRun] at run; cases run
      | ok pair =>
        obtain ⟨tail, finish⟩ := pair
        rw [tailRun] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        exact sessionAllocationSequence_cons pid (snapshot w) d next ok rest tail
          (snapshot finish) pre bound cursor (ih next bounded middle tail finish device tailRun)

end Leanux.Proofs.WG.Index
