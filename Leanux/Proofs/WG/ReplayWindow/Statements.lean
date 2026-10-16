import Leanux.Proofs.WG.Keypairs.Evolution.Runner
import Leanux.Proofs.WG.Keypairs.Evolution.Syscalls

/-! The charter's runner-wide replay theorem and lifetime-aware framing.
S2 and its explicit acceptance/update corollaries are proved in
CounterWindow/Refinement.lean and restated at the end of this file. -/
namespace Leanux.Proofs.WG.ReplayWindow
open Lean Leanux Leanux.WG Leanux.Runner
open Leanux.Proofs.Logged Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.RunnerProof Leanux.Proofs.WG.Keypairs.SyscallObservers
open Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.Framing

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
    (hslot : (snapshot w'.wg).slots slot = some c)
    (hold : c.stamp ≤ (snapshot w.wg).frontier) :
    (snapshot w.wg).slots slot = some c :=
  ((Lifetimes.ProjectedAction.iff_run _ _ _).mp
    (syscall_noReceive_ordinary call hc) w ret w' hr).old_slot hslot hold

/-- Each original validator call keeps the lifetime frontier and every other
slot's entire projected cell, for both true and false results. -/
theorem S3_validator (query nonce : Nat) (w w' : WGWorld) (ambient ambient' : Ambient)
    (history : History) (ok : Bool) (hi : Inv (snapshot w) history)
    (hr : ((counterValidate query nonce).run w).run ambient = .ok ((ok, w'), ambient')) :
    (snapshot w').frontier = (snapshot w).frontier ∧
      ∀ other, other ≠ query → (snapshot w').slots other = (snapshot w).slots other := by
  cases hd : w.dev with
  | none =>
    simp [counterValidate, getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    change (Except.error (.invariant "no WireGuard device in this trace's fixture") :
      Except Stop ((Bool × WGWorld) × Ambient)) = .ok ((ok, w'), ambient') at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[query]? with
    | none =>
      simp [counterValidate, getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      change (Except.error (.invariant s!"dangling keypair {query}") :
        Except Stop ((Bool × WGWorld) × Ambient)) = .ok ((ok, w'), ambient') at hr
      cases hr
    | some k =>
      have hslot := snapshot_lookup w d query k hd hk
      have hs := hi.shaped query (cell k) hslot
      have hex := counterValidate_execution w ambient d query k nonce hd hk hs
      rw [hr] at hex
      have hw := congrArg (fun out => out.1.2) (Except.ok.inj hex)
      dsimp only at hw
      rw [hw, cExecution_snapshot w ambient d query k nonce hd hk]
      constructor
      · rfl
      · intro other ho
        exact put_elsewhere (snapshot w) query other _ ho

/-- Concrete receivingCounter corollary: any lifetime present before and after
a nonreceive syscall retains its counter, even if its slot is described by
different indices. Reachable snapshots supply the stated lifetime invariant. -/
theorem S3_surviving (call : Syscall) (hc : NoReceiveCall call)
    (w w' : World) (ret : Int) (history : History)
    (i j : Nat) (old new : Cell) (hi : Inv (snapshot w.wg) history)
    (hr : (Leanux.syscall call).run w = .ok (ret, w'))
    (hOld : (snapshot w.wg).slots i = some old)
    (hNew : (snapshot w'.wg).slots j = some new)
    (hStamp : old.stamp = new.stamp) :
    old.counter = new.counter := by
  have hb : new.stamp ≤ (snapshot w.wg).frontier := hStamp ▸ hi.bounded i old hOld
  have hAt := S3_nonreceive call hc w w' ret j new hr hNew hb
  have hij := hi.unique i j old new hOld hAt hStamp
  subst j
  have heq : old = new := Option.some.inj (hOld.symm.trans hAt)
  exact congrArg Cell.counter heq

/-- S3, with allocation/deletion and per-validator framing made explicit.
An entire receive-capable batch may contain several named validator events. -/
theorem S3 :
    (∀ call, NoReceiveCall call → ProductOrdinaryAction (Leanux.syscall call)) ∧
    (∀ (query nonce : Nat) (w w' : WGWorld) (ambient ambient' : Ambient) (history : History) (ok : Bool),
      Inv (snapshot w) history →
      ((counterValidate query nonce).run w).run ambient = .ok ((ok, w'), ambient') →
      (snapshot w').frontier = (snapshot w).frontier ∧
        ∀ other, other ≠ query → (snapshot w').slots other = (snapshot w).slots other) :=
  ⟨syscall_noReceive_ordinary, S3_validator⟩

/-- Exact erasure supplies the history for any successful original action;
its checked evolution contract supplies the transition witness. -/
theorem original_success_evolution {α : Type} {g : GhostM α} {o : Leanux.M α}
    (he : Erases g o) (hv : Evolves g) (h : History) (w w' : World) (x : α)
    (hi : Inv (snapshot w.wg) h) (hr : o.run w = .ok (x, w')) :
    ∃ h', ((g.run h).run w) = .ok ((x, h'), w') ∧
      Evolution (snapshot w.wg) h (snapshot w'.wg) h' := by
  have ee := erases_run he h w
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
    (hi : Inv (snapshot w.wg) history)
    (hr : (Leanux.syscall call).run w = .ok (ret, w')) :
    ∃ history', ((syscallLogged call).run history).run w = .ok ((ret, history'), w') ∧
      Evolution (snapshot w.wg) history (snapshot w'.wg) history' :=
  original_success_evolution (syscallLogged_erases call) (syscallLogged_evolves call)
    history w w' ret hi hr

/-- The original action executed between consecutive outer-runner checkpoints. -/
def syscallWithAmbient (call : Syscall) : Leanux.M Int := do
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
  have ambient : SameView (fun w : World => snapshot w.wg) (skipAmbient : Leanux.M Unit) := by
    intro initial
    exact productAmbient_spec AmbientM.skipAmbient (fun w => snapshot w.wg = initial)
      (fun _ _ h => h)
  exact evolves_bind (syscallLogged_evolves call) fun ret =>
    evolves_bind (evolves_liftM (SameView.ordinary ambient)) (fun _ => evolves_pure ret)

/-- The whole-operation S3 form includes the runner's ambient-record step. -/
theorem S3_syscall_ambient (call : Syscall) (w w' : World) (ret : Int) (history : History)
    (hi : Inv (snapshot w.wg) history)
    (hr : (syscallWithAmbient call).run w = .ok (ret, w')) :
    ∃ history', ((syscallWithAmbientLogged call).run history).run w = .ok ((ret, history'), w') ∧
      Evolution (snapshot w.wg) history (snapshot w'.wg) history' :=
  original_success_evolution (syscallWithAmbientLogged_erases call)
    (syscallWithAmbientLogged_evolves call) history w w' ret hi hr

/-- S2, proved in `CounterWindow/Refinement.lean` and restated here so that the
result's terminal statements are all in this file: the fixed mirror's
successful run returns exactly the C-rule result and leaves exactly the C-rule
replay state. The array-shape premise is the C's structure invariant. -/
theorem S2 (w : WGWorld) (ambient : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    ∃ w' ambient', ((counterValidate kp nonce).run w).run ambient = .ok (((step k.receivingCounter nonce).1, w'), ambient') ∧
      counterAt w' kp = some (step k.receivingCounter nonce).2 :=
  Leanux.Proofs.WG.CounterWindow.S2 w ambient d kp k nonce hd hk hsize

/-- S2's acceptance characterization, stated directly for the mirror. -/
theorem S2_acceptance (w : WGWorld) (ambient : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    (∃ w' ambient', ((counterValidate kp nonce).run w).run ambient = .ok ((true, w'), ambient')) ↔
      eligible k.receivingCounter nonce ∧
      (prepared k.receivingCounter (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = false :=
  Leanux.Proofs.WG.CounterWindow.S2_acceptance w ambient d kp k nonce hd hk hsize

/-- S2's accepted-state update, stated directly for the mirror. -/
theorem S2_update (w w' : WGWorld) (ambient ambient' : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128)
    (hrun : ((counterValidate kp nonce).run w).run ambient = .ok ((true, w'), ambient')) :
    counterAt w' kp = some (update k.receivingCounter nonce) :=
  Leanux.Proofs.WG.CounterWindow.S2_update w w' ambient ambient' d kp k nonce hd hk hsize hrun

end Leanux.Proofs.WG.ReplayWindow
