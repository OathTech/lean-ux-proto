import Leanux.Proofs.WG.CounterWindow.Refinement

/-! Replay freedom for finite sequences of calls to the unchanged validator.
This is an executable-mirror intermediate result, not the runner-wide S1. -/
namespace Leanux.Proofs.WG.CounterWindow
open Leanux Leanux.WG

theorem counterAt_some (w : WGWorld) (kp : KeypairId) (c : ReplayCounter)
    (h : counterAt w kp = some c) :
    ∃ d k, w.dev = some d ∧ d.keypairs.get? kp = some k ∧ k.receivingCounter = c := by
  cases hd : w.dev with
  | none => simp [counterAt, hd] at h
  | some d =>
    cases hk : d.keypairs[kp]? with
    | none => simp [counterAt, hd, hk] at h
    | some k =>
      refine ⟨d, k, rfl, hk, ?_⟩
      simpa [counterAt, hd, hk] using h

theorem mirror_step (w : WGWorld) (ambient : Ambient) (kp : KeypairId) (c : ReplayCounter) (nonce : Nat)
    (h : counterAt w kp = some c) (hs : c.backtrack.size = 128) :
    ∃ w' ambient', ((counterValidate kp nonce).run w).run ambient = .ok (((step c nonce).1, w'), ambient') ∧
      counterAt w' kp = some (step c nonce).2 := by
  obtain ⟨d, k, hd, hk, hc⟩ := counterAt_some w kp c h
  simpa [hc] using S2 w ambient d kp k nonce hd hk (by simpa [hc] using hs)

/-- Run only actual mirror calls, retaining exactly their true results. -/
def mirrorCalls (kp : KeypairId) : List Nat → WG.M (List Nat)
  | [] => pure []
  | n :: ns => do
    let ok ← counterValidate kp n
    let rest ← mirrorCalls kp ns
    return if ok then n :: rest else rest

def finish (c : ReplayCounter) : List Nat → ReplayCounter
  | [] => c
  | n :: ns => finish (step c n).2 ns

/-- Exact accepted list and final counter for every finite mirror call list. -/
theorem mirrorCalls_refines (w : WGWorld) (ambient : Ambient) (kp : KeypairId) (c : ReplayCounter)
    (ns : List Nat) (h : counterAt w kp = some c) (hs : c.backtrack.size = 128) :
    ∃ w' ambient', ((mirrorCalls kp ns).run w).run ambient = .ok ((accepted c ns, w'), ambient') ∧
      counterAt w' kp = some (finish c ns) := by
  induction ns generalizing w ambient c with
  | nil => exact ⟨w, ambient, rfl, h⟩
  | cons n ns ih =>
    obtain ⟨mid, midAmbient, hr, hc⟩ := mirror_step w ambient kp c n h hs
    obtain ⟨out, outAmbient, htail, hout⟩ := ih mid midAmbient (step c n).2 hc (by simpa using hs)
    refine ⟨out, outAmbient, ?_, hout⟩
    simp [mirrorCalls, StateT.run_bind, hr, htail, accepted] <;> rfl

/-- No nonce occurs twice among successful calls to the executable validator.
The keypair remains allocated throughout this call-only execution. -/
theorem mirrorCalls_nodup (w w' : WGWorld) (ambient ambient' : Ambient) (kp : KeypairId) (c : ReplayCounter)
    (ns results : List Nat) (h : counterAt w kp = some c)
    (hs : c.backtrack.size = 128)
    (hrun : ((mirrorCalls kp ns).run w).run ambient = .ok ((results, w'), ambient')) : results.Nodup := by
  obtain ⟨out, outAmbient, hr, _⟩ := mirrorCalls_refines w ambient kp c ns h hs
  rw [hrun] at hr
  have heq : results = accepted c ns := congrArg (fun out => out.1.1) (Except.ok.inj hr)
  rw [heq]
  exact accepted_nodup c ns hs

end Leanux.Proofs.WG.CounterWindow
