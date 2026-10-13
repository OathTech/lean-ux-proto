import Leanux.Spikes.EvolutionRunner
import Leanux.Spikes.EvolutionSyscalls

/-! The charter's runner-wide replay theorem and lifetime-aware framing.
S2 and its explicit acceptance/update corollaries are in Refinement.lean. -/
namespace Leanux.Spikes
open Lean Leanux Leanux.WG Leanux.Runner
open Ghost Lifetimes Lifetimes.RunnerProof Lifetimes.SyscallObservers
open Window

/-- S1: every accepted execution has its exact source-call acceptance history,
and no two events share an allocation lifetime and wire counter. The history
records every committed true original validator return, including packets dropped
later; discarded scheduler consistency probes do not commit World or history. -/
theorem S1 (trace : Trace) (placeholders : Bool) (json : Json)
    (accepted : Runner.executeTrace trace placeholders = .ok json) :
    ∃ history, (executeTraceLogged trace placeholders).run [] = .ok (json, history) ∧
      history.Nodup :=
  executeTrace_accepted_nodup trace placeholders json accepted

/-- Original nonreceive syscalls preserve every surviving old cell exactly.
Fresh allocation and deletion are permitted; the frontier bound identifies
lifetimes that already existed before the operation. -/
theorem S3_nonreceive (call : Syscall) (hc : NoReceiveCall call)
    (w w' : World) (ret : Int) (slot : Nat) (c : Cell)
    (hr : (Leanux.syscall call).run w = .ok (ret, w'))
    (hslot : (snapshot w').slots slot = some c)
    (hold : c.stamp ≤ (snapshot w).frontier) :
    (snapshot w).slots slot = some c :=
  (syscall_noReceive_ordinary call hc w ret w' hr).old_slot hslot hold

/-- Each original validator call keeps the lifetime frontier and every other
slot's entire projected cell, for both true and false results. -/
theorem S3_validator (query nonce : Nat) (w w' : World)
    (history : History) (ok : Bool) (hi : Inv (snapshot w) history)
    (hr : (counterValidate query nonce).run w = .ok (ok, w')) :
    (snapshot w').frontier = (snapshot w).frontier ∧
      ∀ other, other ≠ query → (snapshot w').slots other = (snapshot w).slots other := by
  cases hd : w.k.wg with
  | none => simp [counterValidate, getKeypair, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hk : d.keypairs[query]? with
    | none => simp [counterValidate, getKeypair, getDev, getK, hd, hk, invariant] at hr
    | some k =>
      have hslot := snapshot_lookup w d query k hd hk
      have hs := hi.shaped query (cell k) hslot
      have hex := counterValidate_execution w d query k nonce hd hk hs
      rw [hr] at hex
      have hw := congrArg Prod.snd (Except.ok.inj hex)
      dsimp only at hw
      rw [hw, cExecution_snapshot w d query k nonce hd hk]
      constructor
      · rfl
      · intro other ho
        exact put_elsewhere (snapshot w) query other _ ho

/-- Concrete receivingCounter corollary: any lifetime present before and after
a nonreceive syscall retains its counter, even if its slot is described by
different indices. Reachable snapshots supply the stated lifetime invariant. -/
theorem S3_surviving (call : Syscall) (hc : NoReceiveCall call)
    (w w' : World) (ret : Int) (history : History)
    (i j : Nat) (old new : Cell) (hi : Inv (snapshot w) history)
    (hr : (Leanux.syscall call).run w = .ok (ret, w'))
    (hOld : (snapshot w).slots i = some old)
    (hNew : (snapshot w').slots j = some new)
    (hStamp : old.stamp = new.stamp) :
    old.counter = new.counter := by
  have hb : new.stamp ≤ (snapshot w).frontier := hStamp ▸ hi.bounded i old hOld
  have hAt := S3_nonreceive call hc w w' ret j new hr hNew hb
  have hij := hi.unique i j old new hOld hAt hStamp
  subst j
  have heq : old = new := Option.some.inj (hOld.symm.trans hAt)
  exact congrArg Cell.counter heq

/-- S3, with allocation/deletion and per-validator framing made explicit.
An entire receive-capable batch may contain several named validator events. -/
theorem S3 :
    (∀ call, NoReceiveCall call → OrdinaryAction (Leanux.syscall call)) ∧
    (∀ (query nonce : Nat) (w w' : World) (history : History) (ok : Bool),
      Inv (snapshot w) history →
      (counterValidate query nonce).run w = .ok (ok, w') →
      (snapshot w').frontier = (snapshot w).frontier ∧
        ∀ other, other ≠ query → (snapshot w').slots other = (snapshot w).slots other) :=
  ⟨syscall_noReceive_ordinary, S3_validator⟩

/-- Exact erasure supplies the history for any successful original action;
its checked evolution contract supplies the transition witness. -/
theorem original_success_evolution {α : Type} {g : GhostM α} {o : M α}
    (he : Erases g o) (hv : Evolves g) (h : History) (w w' : World) (x : α)
    (hi : Inv (snapshot w) h) (hr : o.run w = .ok (x, w')) :
    ∃ h', ((g.run h).run w) = .ok ((x, h'), w') ∧
      Evolution (snapshot w) h (snapshot w') h' := by
  have ee := he h w
  rw [hr] at ee
  cases hg : ((g.run h).run w) with
  | error e => simp [hg, eraseResult] at ee
  | ok out =>
    rcases out with ⟨⟨y, h'⟩, v⟩
    rw [hg] at ee
    change Except.ok (y, v) = Except.ok (x, w') at ee
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ee)
    exact ⟨h', rfl, hv h w y h' v hi hg⟩

/-- Whole-syscall S3 over the original executable action: every final projected
cell is connected to the starting store by ordinary lifecycle transitions and
exact named validator transitions. This includes return-to-user scheduling. -/
theorem S3_syscall (call : Syscall) (w w' : World) (ret : Int) (history : History)
    (hi : Inv (snapshot w) history)
    (hr : (Leanux.syscall call).run w = .ok (ret, w')) :
    ∃ history', ((syscallLogged call).run history).run w = .ok ((ret, history'), w') ∧
      Evolution (snapshot w) history (snapshot w') history' :=
  original_success_evolution (syscallLogged_erases call) (syscallLogged_evolves call)
    history w w' ret hi hr

/-- The original action executed between consecutive outer-runner checkpoints. -/
def syscallWithAmbient (call : Syscall) : M Int := do
  let ret ← Leanux.syscall call
  skipAmbient
  return ret

/-- The same committed action with the checked acceptance observer. -/
def syscallWithAmbientLogged (call : Syscall) : GhostM Int := do
  let ret ← syscallLogged call
  skipAmbient
  return ret

theorem syscallWithAmbientLogged_erases (call : Syscall) :
    Erases (syscallWithAmbientLogged call) (syscallWithAmbient call) := by
  unfold syscallWithAmbientLogged syscallWithAmbient
  exact erases_bind (syscallLogged_erases call) fun ret =>
    erases_bind (erases_liftM skipAmbient) (fun _ => erases_pure ret)

theorem syscallWithAmbientLogged_evolves (call : Syscall) :
    Evolves (syscallWithAmbientLogged call) := by
  unfold syscallWithAmbientLogged
  exact evolves_bind (syscallLogged_evolves call) fun ret =>
    evolves_bind (evolves_liftM (sameSnapshot_of_sameKernel
      Framing.skipAmbient_sameKernel).ordinary) (fun _ => evolves_pure ret)

/-- The whole-operation S3 form includes the runner's ambient-record step. -/
theorem S3_syscall_ambient (call : Syscall) (w w' : World) (ret : Int) (history : History)
    (hi : Inv (snapshot w) history)
    (hr : (syscallWithAmbient call).run w = .ok (ret, w')) :
    ∃ history', ((syscallWithAmbientLogged call).run history).run w = .ok ((ret, history'), w') ∧
      Evolution (snapshot w) history (snapshot w') history' :=
  original_success_evolution (syscallWithAmbientLogged_erases call)
    (syscallWithAmbientLogged_evolves call) history w w' ret hi hr

end Leanux.Spikes
