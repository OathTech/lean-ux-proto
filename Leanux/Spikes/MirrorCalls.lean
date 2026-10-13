import Leanux.Spikes.Refinement

/-! Replay freedom for finite sequences of calls to the unchanged validator.
This is an executable-mirror intermediate result, not the runner-wide S1. -/
namespace Leanux.Spikes.Window
open Leanux Leanux.WG

theorem counterAt_some (w : World) (kp : KeypairId) (c : ReplayCounter)
    (h : counterAt w kp = some c) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs.get? kp = some k ∧ k.receivingCounter = c := by
  cases hd : w.k.wg with
  | none => simp [counterAt, hd] at h
  | some d =>
    cases hk : d.keypairs[kp]? with
    | none => simp [counterAt, hd, hk] at h
    | some k =>
      refine ⟨d, k, rfl, hk, ?_⟩
      simpa [counterAt, hd, hk] using h

theorem mirror_step (w : World) (kp : KeypairId) (c : ReplayCounter) (nonce : Nat)
    (h : counterAt w kp = some c) (hs : c.backtrack.size = 128) :
    ∃ w', (counterValidate kp nonce).run w = .ok ((step c nonce).1, w') ∧
      counterAt w' kp = some (step c nonce).2 := by
  obtain ⟨d, k, hd, hk, hc⟩ := counterAt_some w kp c h
  simpa [hc] using S2 w d kp k nonce hd hk (by simpa [hc] using hs)

/-- Run only actual mirror calls, retaining exactly their true results. -/
def mirrorCalls (kp : KeypairId) : List Nat → M (List Nat)
  | [] => pure []
  | n :: ns => do
    let ok ← counterValidate kp n
    let rest ← mirrorCalls kp ns
    return if ok then n :: rest else rest

def finish (c : ReplayCounter) : List Nat → ReplayCounter
  | [] => c
  | n :: ns => finish (step c n).2 ns

/-- Exact accepted list and final counter for every finite mirror call list. -/
theorem mirrorCalls_refines (w : World) (kp : KeypairId) (c : ReplayCounter)
    (ns : List Nat) (h : counterAt w kp = some c) (hs : c.backtrack.size = 128) :
    ∃ w', (mirrorCalls kp ns).run w = .ok (accepted c ns, w') ∧
      counterAt w' kp = some (finish c ns) := by
  induction ns generalizing w c with
  | nil => exact ⟨w, rfl, h⟩
  | cons n ns ih =>
    obtain ⟨mid, hr, hc⟩ := mirror_step w kp c n h hs
    obtain ⟨out, htail, hout⟩ := ih mid (step c n).2 hc (by simpa using hs)
    refine ⟨out, ?_, hout⟩
    simp [mirrorCalls, StateT.run_bind, hr, htail, accepted] <;> rfl

/-- No nonce occurs twice among successful calls to the executable validator.
The keypair remains allocated throughout this call-only execution. -/
theorem mirrorCalls_nodup (w w' : World) (kp : KeypairId) (c : ReplayCounter)
    (ns results : List Nat) (h : counterAt w kp = some c)
    (hs : c.backtrack.size = 128)
    (hrun : (mirrorCalls kp ns).run w = .ok (results, w')) : results.Nodup := by
  obtain ⟨out, hr, _⟩ := mirrorCalls_refines w kp c ns h hs
  rw [hrun] at hr
  have heq : results = accepted c ns := congrArg Prod.fst (Except.ok.inj hr)
  rw [heq]
  exact accepted_nodup c ns hs

end Leanux.Spikes.Window
