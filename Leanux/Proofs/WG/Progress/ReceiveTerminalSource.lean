import Leanux.Proofs.WG.Progress.ReceiveTerminalModel
import Leanux.Proofs.WG.Progress.CookieActivationSource
import Leanux.Proofs.WG.Progress.RecordSuffixSource
import Leanux.Proofs.WG.Progress.ActivationExitSource

/-! Exact original empty-return classification and final receive cut. The nonempty
packet arm is ruled out only for a false return; its callbacks are not replaced
or assumed to preserve records. The existing activation audit supplies the
same actual last iteration and section-stop action, including failures. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem receiveStep_false_cut (g v : WGWorld) (a b : Ambient)
    (run : ((WG.receiveStep.run g).run a) = .ok ((false,v),b)) :
    ∃ d, g.dev = some d ∧ d.handshakeQueue.peek = none ∧
      v = g ∧ b.hidden = a.hidden := by
  unfold WG.receiveStep at run
  simp only [StateT.run_bind] at run
  cases device : g.dev with
  | none =>
    simp [getDev,device] at run
    change Except.error (.invariant "no WireGuard device in this trace's fixture") =
      (.ok ((false,v),b) : Except Stop ((Bool × WGWorld) × Ambient)) at run
    cases run
  | some d =>
    have read : ((getDev.run g).run a) = .ok ((d,g),a) := by
      simp [getDev,device]
      rfl
    rw [read] at run
    simp only [bind,Except.bind] at run
    cases empty : d.handshakeQueue.peek with
    | none =>
      simp only [PtrRing.consume,empty] at run
      simp [branch,AmbientM.branch] at run
      obtain ⟨rfl,rfl⟩ := run
      exact ⟨d,rfl,empty,rfl,rfl⟩
    | some item =>
      rcases item with ⟨msg,src⟩
      simp only [PtrRing.consume,empty] at run
      simp only [StateT.run, StateT.bind, bind, Except.bind] at run
      repeat' first | split at run | cases run

theorem receiveStep_product_false_cut (w v : World)
    (run : (liftWG WG.receiveStep).run w = .ok (false,v)) :
    ∃ d, w.wg.dev = some d ∧ d.handshakeQueue.peek = none ∧
      v.wg = w.wg ∧ v.ambient.hidden = w.ambient.hidden := by
  rw [liftWG_run] at run
  cases native : ((WG.receiveStep.run w.wg).run w.ambient) with
  | error e => rw [native] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value,g⟩,a⟩
    rw [native] at run
    cases run
    exact receiveStep_false_cut _ _ _ _ native

theorem receive_iteration_ended_cut (active : Activation)
    (receive : active.worker = .receiveWorker) (w v : World)
    (run : (Activation.iter active).run w = .ok (.ended,v)) :
    ∃ d, w.wg.dev = some d ∧ d.handshakeQueue.peek = none ∧
      v.wg = w.wg ∧ v.ambient.hidden = w.ambient.hidden := by
  have lift : (liftM WG.receiveStep : Leanux.M Bool) = liftWG WG.receiveStep := rfl
  simp only [Activation.iter, receive, workerIter, StateT.run_bind, lift] at run
  cases step : (liftWG WG.receiveStep).run w with
  | error e => rw [step] at run; cases run
  | ok pair =>
    rcases pair with ⟨worked,middle⟩
    rw [step] at run
    cases worked with
    | false =>
      cases run
      exact receiveStep_product_false_cut _ _ step
    | true =>
      simp only [bind,Except.bind,Bool.not_true,Bool.false_eq_true,ite_false] at run
      simp only [StateT.run,StateT.bind,bind,Except.bind] at run
      split at run
      · cases run
      · split at run <;> cases run

theorem receive_terminal_strict (active : Activation)
    (receive : active.worker = .receiveWorker) (w middle final : World)
    (records : List HiddenRecord) (bytes : List UInt8)
    (present : w.ambient.hidden = some records)
    (iteration : (Activation.iter active).run w = .ok (.ended,middle))
    (stop : (hidden (.sectionStop active.worker) : Leanux.M (List UInt8)).run middle =
      .ok (bytes,final)) :
    StrictTail records final.ambient.hidden := by
  obtain ⟨_,_,_,_,same⟩ := receive_iteration_ended_cut active receive w middle iteration
  exact (hoare_iff_run _ _ _).mp
    (hidden_product_suffix (.sectionStop active.worker) records)
    middle bytes final (same.trans present) stop

theorem receive_empty_activation_strict (active : Activation)
    (receive : active.worker = .receiveWorker) (w final : World) (d : Device)
    (records : List HiddenRecord)
    (device : w.wg.dev = some d) (empty : d.handshakeQueue.peek = none)
    (present : w.ambient.hidden = some records)
    (run : (Activation.run active).run w = .ok ((),final)) :
    StrictTail records final.ambient.hidden := by
  rw [cookieEmptyActivation_run active receive w d records device empty present] at run
  cases read : resolveCookieRead false records with
  | error e => rw [read] at run; cases run
  | ok pair =>
    rcases pair with ⟨bytes,rest⟩
    rw [read] at run
    cases run
    obtain ⟨suffix,shorter⟩ := resolveCookieRead_suffix false records bytes rest read
    exact ⟨rest,rfl,suffix,shorter⟩

theorem receive_activation_terminal (active : Activation)
    (receive : active.worker = .receiveWorker) (initial : World) :
    ReceiveTerminal ((activationExitRun active initial).map Campaign2.Product.snapshot) := by
  have sources := activationExitRun_source_facts active initial
  have facts := activationExitRun_facts active initial
  cases audit : activationExitRun active initial with
  | occupancyError e => trivial
  | ran occupancy entry result =>
    cases result with
    | iterationError count current before e => trivial
    | yielded count current before middle final => trivial
    | exhausted count current before e => trivial
    | ended count current before middle stop =>
      rw [audit] at sources facts
      have same : current = {active with iterations := active.iterations + count} := facts.2.1
      have worker : current.worker = .receiveWorker := by rw [same]; exact receive
      obtain ⟨d,device,empty,wg,hiddenEq⟩ :=
        receive_iteration_ended_cut current worker before middle sources.2.1
      change (∃ d, before.wg.dev = some d ∧ d.handshakeQueue.peek = none) ∧
        (Campaign2.snapshot middle.wg middle.ambient).wg =
          (Campaign2.snapshot before.wg before.ambient).wg ∧
        middle.ambient.hidden = before.ambient.hidden ∧ _
      refine ⟨⟨d,device,empty⟩,?_,hiddenEq,?_⟩
      · rw [wg]; rfl
      · intro records present bytes final normal
        cases stop with
        | error e => cases normal
        | ok pair =>
          rcases pair with ⟨actualBytes,actualFinal⟩
          cases normal
          exact receive_terminal_strict current worker before middle actualFinal
            records bytes present sources.2.1 sources.2.2
end Leanux.Proofs.WG.Progress.RecordSuffix


