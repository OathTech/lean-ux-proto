import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDispatch
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Source-cut history on the initialized shared driver, including indexed
Stops. The H1 slot-edge obligation remains a named premise; live carrier
invariants are derived from the actual runner initialization. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem initialized_safe (H1 : H1ResponderCurrentEdges) (trace : Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 := by
  apply RunnerInvariant.executeTraceWith ProductInv Safe
    (fun _ _ hi => hi.2) product_wg_stable (Driver.syscallObserved hooks)
    (syscall H1) trace placeholders
  intro w same
  apply product_wg_stable [] {w with wg := initialWG trace.net trace.bare} w same
  exact initial trace.net trace.bare

/-- Each selected/current, confirmation or session cut carries the actual
native execution and the carrier derived from this trace's initialization.
The event remains checked even when a later caller or runner step stops. -/
theorem initialized_cut (H1 : H1ResponderCurrentEdges) (trace : Trace) (placeholders : Bool)
    (pre post : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ event :: post) :
    Checked pre event :=
  initialized_safe H1 trace placeholders pre event post position

/-- The selected responder material is authorized by an earlier confirmation
in this exact initialized journal. The material may be read after selection:
the native queue-clear and key borrow supply that frame. -/
theorem initialized_selected (H1 : H1ResponderCurrentEdges) (trace : Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ .selected pid r :: post)
    (p : Peer) (kid : KeypairId) (selected : r.value = some (p,some kid))
    (core : KeyCore) (material : pool r.after kid = some core) (responder : core.initiator = false) :
    core.allocation ∈ labels pre := by
  obtain ⟨entry,valid⟩ := initialized_cut H1 trace placeholders pre post (.selected pid r) position
  exact selected_after_material pid r valid p kid selected core material _ entry.2.1 responder

/-- Strict temporal precedence is represented by a source event in the prefix
before selection. This receipt proves a successful native confirmation, not
yet the authenticated transport provenance of its caller. -/
def PriorNativeConfirmation (pre : List Event) (allocation : Nat) : Prop :=
  ∃ left right pid kid, ∃ r : WGRunWitness Bool, ∃ core : KeyCore,
    pre = left ++ .confirmed pid kid r :: right ∧
    r.Valid (receivedWithKeypair pid kid) ∧ r.value = true ∧
    keyCoreAt r.before kid = some core ∧ core.allocation = allocation

theorem earlier_native_confirmation (H1 : H1ResponderCurrentEdges)
    (trace : Trace) (placeholders : Bool) (pre post : List Event) (event : Event)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ event :: post)
    (allocation : Nat) (member : allocation ∈ labels pre) : PriorNativeConfirmation pre allocation := by
  obtain ⟨prior,inside,label⟩ := List.mem_flatMap.mp member
  cases prior with
  | selected _ _ => cases label
  | session _ _ => cases label
  | confirmed pid kid r =>
    change allocation ∈ confirmedAt r.before kid r.value at label
    cases accepted : r.value with
    | false => simp [confirmedAt,accepted] at label
    | true =>
      cases material : keyCoreAt r.before kid with
      | none => simp [confirmedAt,accepted,material] at label
      | some core =>
        have equal : core.allocation = allocation := by
          have eq : allocation = core.allocation := by
            simpa [confirmedAt,accepted,material] using label
          exact eq.symm
        obtain ⟨left,right,split⟩ := List.mem_iff_append.mp inside
        have earlier : (runPrefixOuter (execute trace placeholders) []).2 =
            left ++ .confirmed pid kid r :: (right ++ event :: post) := by
          rw [position,split]
          simp only [List.append_assoc,List.cons_append]
        exact ⟨left,right,pid,kid,r,core,split,
          (initialized_cut H1 trace placeholders left _ _ earlier).2,accepted,material,equal⟩

theorem initialized_selected_prior_confirmation
    (H1 : H1ResponderCurrentEdges) (trace : Trace) (placeholders : Bool)
    (pre post : List Event) (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ .selected pid r :: post)
    (p : Peer) (kid : KeypairId) (selected : r.value = some (p,some kid))
    (core : KeyCore) (material : pool r.after kid = some core) (responder : core.initiator = false) :
    PriorNativeConfirmation pre core.allocation :=
  earlier_native_confirmation H1 trace placeholders pre post _ position core.allocation
    (initialized_selected H1 trace placeholders pre post pid r position p kid selected core material responder)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
